import MerLeanExperiment.Certificates.Z12Direct_5_8_5.Inputs

/-! Generated from the actual pinned z12direct_5_8_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c529 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c65, some c114, some c150, some c156, some c207, some c248, some c197, some c354, some c51, some c356, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p529 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 31) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c66, c65, c114, c150, c156, c207, c248, c197, c354, c51, c356] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c248 := h 247 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c354 := h 353 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c71, some c66, some c529, some c77, some c89, some c59, some c160, some c319, some c13, some c130, some c191, some c263, some c189, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p530 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 31) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c71, c66, c529, c77, c89, c59, c160, c319, c13, c130, c191, c263, c189] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c529 := derived529 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c130 := h 129 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c77, some c160, some c13, some c14, some c191, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p531 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 31) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c77, c160, c13, c14, c191] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨5, by decide⟩, false), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c530, some c531, some c65, some c59, some c160, some c191, some c51, some c189, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p532 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 31) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c530, c531, c65, c59, c160, c191, c51, c189] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c531 := derived531 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c530, some c531, some c114, some c65, some c71, some c532, some c326, some c265, some c157, some c178, some c294, some c320, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p533 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 31) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c530, c531, c114, c65, c71, c532, c326, c265, c157, c178, c294, c320] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c531 := derived531 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c532 := derived532 a h
  have h6 : Entails.eval a c326 := h 325 (by decide)
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c157 := h 156 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c530, some c531, some c65, some c114, some c533, some c207, some c156, some c206, some c209, some c374, some c250, some c52, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p534 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 31) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c530, c531, c65, c114, c533, c207, c156, c206, c209, c374, c250, c52] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c531 := derived531 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c533 := derived533 a h
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c374 := h 373 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c106, some c52, some c59, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p535 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 31) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c106, c52, c59] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨23, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c88, some c95, some c73, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p536 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 31) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c88, c95, c73] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c88 := h 87 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c530, some c534, some c536, some c106, some c535, some c84, some c98, some c74, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p537 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 31) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c530, c534, c536, c106, c535, c84, c98, c74] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c534 := derived534 a h
  have h2 : Entails.eval a c536 := derived536 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c535 := derived535 a h
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨23, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c536, some c106, some c160, some c66, some c167, some c235, some c173, some c341, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p538 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 31) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c536, c106, c160, c66, c167, c235, c173, c341] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c536 := derived536 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c167 := h 166 (by decide)
  have h5 : Entails.eval a c235 := h 234 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c537, some c66, some c536, some c106, some c538, some c50, some c84, some c52, some c101, some c166, some c180, some c234, some c272, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p539 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 31) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c537, c66, c536, c106, c538, c50, c84, c52, c101, c166, c180, c234, c272] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c536 := derived536 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c538 := derived538 a h
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c180 := h 179 (by decide)
  have h11 : Entails.eval a c234 := h 233 (by decide)
  have h12 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c539, some c531, some c537, some c84, some c121, some c52, some c133, some c194, some c62, some c272, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p540 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 31) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c539, c531, c537, c84, c121, c52, c133, c194, c62, c272] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c539 := derived539 a h
  have h1 : Entails.eval a c531 := derived531 a h
  have h2 : Entails.eval a c537 := derived537 a h
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c194 := h 193 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c537, some c160, some c540, some c50, some c167, some c235, some c173, some c341, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p541 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 31) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c537, c160, c540, c50, c167, c235, c173, c341] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c540 := derived540 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c167 := h 166 (by decide)
  have h5 : Entails.eval a c235 := h 234 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c539, some c531, some c114, some c541, some c31, some c156, some c209, some c30, some c265, some c240, some c206, some c25, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p542 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 31) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c539, c531, c114, c541, c31, c156, c209, c30, c265, c240, c206, c25] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c539 := derived539 a h
  have h1 : Entails.eval a c531 := derived531 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c541 := derived541 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c240 := h 239 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c30, some c156, some c207, some c265, some c238, some c208, some c25, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p543 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 31) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c30, c156, c207, c265, c238, c208, c25] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c238 := h 237 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c539, some c537, some c71, some c531, some c114, some c542, some c60, some c543, some c160, some c188, some c191, some c178, some c263, some c208, some c386, some c423, some c451, some c381, some c194, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p544 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 31) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c539, c537, c71, c531, c114, c542, c60, c543, c160, c188, c191, c178, c263, c208, c386, c423, c451, c381, c194] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c539 := derived539 a h
  have h1 : Entails.eval a c537 := derived537 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c531 := derived531 a h
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c542 := derived542 a h
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c543 := derived543 a h
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c178 := h 177 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c386 := h 385 (by decide)
  have h15 : Entails.eval a c423 := h 422 (by decide)
  have h16 : Entails.eval a c451 := h 450 (by decide)
  have h17 : Entails.eval a c381 := h 380 (by decide)
  have h18 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c545 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c544, some c539, some c60, some c89, some c105, some c114, some c160, some c150, some c188, some c238, some c197, some c73, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p545 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 31) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c544, c539, c60, c89, c105, c114, c160, c150, c188, c238, c197, c73] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c544 := derived544 a h
  have h1 : Entails.eval a c539 := derived539 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c150 := h 149 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c238 := h 237 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c160, some c545, some c544, some c539, some c537, some c114, some c150, some c156, some c207, some c252, some c248, some c197, some c386, some c418, some c133, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p546 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 31) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c160, c545, c544, c539, c537, c114, c150, c156, c207, c252, c248, c197, c386, c418, c133] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c544 := derived544 a h
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c537 := derived537 a h
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c386 := h 385 (by decide)
  have h13 : Entails.eval a c418 := h 417 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c545, some c544, some c539, some c160, some c546, some c13, some c191, some c189, some c263, some c205, some c197, some c252, some c8, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p547 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 31) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c545, c544, c539, c160, c546, c13, c191, c189, c263, c205, c197, c252, c8] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c545 := derived545 a h
  have h1 : Entails.eval a c544 := derived544 a h
  have h2 : Entails.eval a c539 := derived539 a h
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c546 := derived546 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c544, some c547, some c105, some c93, some c86, some c73, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p548 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 31) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c544, c547, c105, c93, c86, c73] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c544 := derived544 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c93, some c86, some c73, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p549 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 31) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c93, c86, c73] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c548, some c71, some c66, some c549, some c105, some c160, some c15, some c157, some c73, some c111, some c382, some c484, some c67, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p550 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 31) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c548, c71, c66, c549, c105, c160, c15, c157, c73, c111, c382, c484, c67] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c548 := derived548 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c549 := derived549 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c484 := h 483 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c550, some c548, some c71, some c15, some c157, some c73, some c111, some c335, some c436, some c67, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p551 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 31) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c550, c548, c71, c15, c157, c73, c111, c335, c436, c67] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c550 := derived550 a h
  have h1 : Entails.eval a c548 := derived548 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c335 := h 334 (by decide)
  have h8 : Entails.eval a c436 := h 435 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c71, some c548, some c550, some c551, some c160, some c77, some c114, some c38, some c111, some c73, some c157, some c326, some c426, some c69, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p552 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 31) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c71, c548, c550, c551, c160, c77, c114, c38, c111, c73, c157, c326, c426, c69] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c548 := derived548 a h
  have h2 : Entails.eval a c550 := derived550 a h
  have h3 : Entails.eval a c551 := derived551 a h
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  have h12 : Entails.eval a c426 := h 425 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c81, some c164, some c169, some c61, some c57, some c178, some c238, some c209, some c124, some c479, some c317, some c147, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p553 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 31) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c552, c81, c164, c169, c61, c57, c178, c238, c209, c124, c479, c317, c147] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c169 := h 168 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c238 := h 237 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c479 := h 478 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c378, some c480, some c97, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p554 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 31) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c378, c480, c97] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c480 := h 479 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c426, some c554, some c109, some c94, some c315, some c330, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p555 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 31) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c426, c554, c109, c94, c315, c330] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c426 := h 425 (by decide)
  have h1 : Entails.eval a c554 := derived554 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c124, some c54, some c198, some c169, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p556 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 31) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c124, c54, c198, c169] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨1, by decide⟩, true), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c556, some c553, some c555, some c57, some c170, some c50, some c239, some c190, some c161, some c97, some c263, some c10, some c183, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p557 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 31) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c552, c556, c553, c555, c57, c170, c50, c239, c190, c161, c97, c263, c10, c183] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c553 := derived553 a h
  have h3 : Entails.eval a c555 := derived555 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c239 := h 238 (by decide)
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c556, some c553, some c557, some c64, some c468, some c35, some c414, some c470, some c109, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p558 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 31) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c552, c556, c553, c557, c64, c468, c35, c414, c470, c109] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c553 := derived553 a h
  have h3 : Entails.eval a c557 := derived557 a h
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c468 := h 467 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c414 := h 413 (by decide)
  have h8 : Entails.eval a c470 := h 469 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨28, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c303, some c359, some c156, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p559 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 31) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c303, c359, c156] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c303 := h 302 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨28, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c462, some c400, some c156, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p560 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 31) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c462, c400, c156] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c462 := h 461 (by decide)
  have h1 : Entails.eval a c400 := h 399 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c559, some c133, some c560, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p561 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 31) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c559, c133, c560] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c560 := derived560 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c553, some c556, some c558, some c561, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p562 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 31) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c552, c553, c556, c558, c561] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c553 := derived553 a h
  have h2 : Entails.eval a c556 := derived556 a h
  have h3 : Entails.eval a c558 := derived558 a h
  have h4 : Entails.eval a c561 := derived561 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c90, some c72, some c65, some c74, some c131, some c158, some c507, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p563 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 31) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c90, c72, c65, c74, c131, c158, c507] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c90 := h 89 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c507 := h 506 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c64, some c69, some c92, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p564 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 31) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c64, c69, c92] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c64 := h 63 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨29, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c564, some c90, some c563, some c74, some c158, some c474, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p565 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 31) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c564, c90, c563, c74, c158, c474] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c564 := derived564 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c563 := derived563 a h
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c474 := h 473 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c48, some c565, some c43, some c81, some c164, some c90, some c10, some c113, some c455, some c39, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p566 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 31) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c48, c565, c43, c81, c164, c90, c10, c113, c455, c39] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c164 := h 163 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c455 := h 454 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c48, some c565, some c43, some c566, some c69, some c35, some c371, some c485, some c388, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p567 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 31) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c48, c565, c43, c566, c69, c35, c371, c485, c388] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c566 := derived566 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c485 := h 484 (by decide)
  have h8 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨11, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c565, some c81, some c164, some c208, some c69, some c486, some c92, some c460, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p568 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 31) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c565, c81, c164, c208, c69, c486, c92, c460] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c565 := derived565 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c486 := h 485 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c460 := h 459 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c562, some c48, some c565, some c81, some c164, some c567, some c208, some c25, some c568, some c90, some c436, some c113, some c456, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p569 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 31) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c552, c562, c48, c565, c81, c164, c567, c208, c25, c568, c90, c436, c113, c456] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c562 := derived562 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c565 := derived565 a h
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c567 := derived567 a h
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c568 := derived568 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c436 := h 435 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c456 := h 455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c565, some c81, some c164, some c569, some c208, some c568, some c25, some c90, some c436, some c299, some c113, some c92, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p570 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 31) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c552, c565, c81, c164, c569, c208, c568, c25, c90, c436, c299, c113, c92] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c569 := derived569 a h
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c568 := derived568 a h
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c436 := h 435 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c565, some c81, some c164, some c90, some c10, some c113, some c222, some c187, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p571 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 31) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c565, c81, c164, c90, c10, c113, c222, c187] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c565 := derived565 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c222 := h 221 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c569, some c552, some c565, some c81, some c164, some c570, some c43, some c571, some c397, some c168, some c263, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p572 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 31) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c569, c552, c565, c81, c164, c570, c43, c571, c397, c168, c263] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c569 := derived569 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c565 := derived565 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c164 := h 163 (by decide)
  have h5 : Entails.eval a c570 := derived570 a h
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c571 := derived571 a h
  have h8 : Entails.eval a c397 := h 396 (by decide)
  have h9 : Entails.eval a c168 := h 167 (by decide)
  have h10 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c569, some c54, some c88, some c89, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p573 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 31) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c569, c54, c88, c89] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c569 := derived569 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c573, some c572, some c569, some c552, some c88, some c169, some c61, some c57, some c178, some c238, some c30, some c481, some c377, some c554, some c138, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p574 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 31) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c573, c572, c569, c552, c88, c169, c61, c57, c178, c238, c30, c481, c377, c554, c138] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c572 := derived572 a h
  have h2 : Entails.eval a c569 := derived569 a h
  have h3 : Entails.eval a c552 := derived552 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c178 := h 177 (by decide)
  have h9 : Entails.eval a c238 := h 237 (by decide)
  have h10 : Entails.eval a c30 := h 29 (by decide)
  have h11 : Entails.eval a c481 := h 480 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c554 := derived554 a h
  have h14 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨23, by decide⟩, true), (⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c78, some c554, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p575 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 31) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c78, c554] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c554 := derived554 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c576 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨23, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c575, some c161, some c328, some c428, some c97, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p576 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 31) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c575, c161, c328, c428, c97] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c161 := h 160 (by decide)
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c428 := h 427 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c265, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p577 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 31) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c209, c265] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c209 := h 208 (by decide)
  have h1 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c578 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c328, some c428, some c97, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p578 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 31) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c328, c428, c97] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c428 := h 427 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c573, some c572, some c574, some c81, some c170, some c561, some c239, some c577, some c232, some c578, some c424, some c449, some c401, some c161, some c26, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p579 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 31) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c552, c573, c572, c574, c81, c170, c561, c239, c577, c232, c578, c424, c449, c401, c161, c26] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c573 := derived573 a h
  have h2 : Entails.eval a c572 := derived572 a h
  have h3 : Entails.eval a c574 := derived574 a h
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c561 := derived561 a h
  have h7 : Entails.eval a c239 := h 238 (by decide)
  have h8 : Entails.eval a c577 := derived577 a h
  have h9 : Entails.eval a c232 := h 231 (by decide)
  have h10 : Entails.eval a c578 := derived578 a h
  have h11 : Entails.eval a c424 := h 423 (by decide)
  have h12 : Entails.eval a c449 := h 448 (by decide)
  have h13 : Entails.eval a c401 := h 400 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c81, some c578, some c579, some c191, some c576, some c161, some c115, some c263, some c298, some c396, some c41, some c39, some c133, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p580 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 31) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c552, c81, c578, c579, c191, c576, c161, c115, c263, c298, c396, c41, c39, c133] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c578 := derived578 a h
  have h3 : Entails.eval a c579 := derived579 a h
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c576 := derived576 a h
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c396 := h 395 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨11, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c298, some c396, some c41, some c39, some c133, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p581 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 31) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c81, c298, c396, c41, c39, c133] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c396 := h 395 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c39, some c16, some c177, some c234, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p582 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 31) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c39, c16, c177, c234] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c578, some c581, some c582, some c70, some c58, some c175, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p583 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 31) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c81, c578, c581, c582, c70, c58, c175] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c578 := derived578 a h
  have h2 : Entails.eval a c581 := derived581 a h
  have h3 : Entails.eval a c582 := derived582 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c81, some c579, some c578, some c580, some c583, some c156, some c262, some c298, some c396, some c18, some c16, some c180, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p584 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 31) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c552, c81, c579, c578, c580, c583, c156, c262, c298, c396, c18, c16, c180] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c579 := derived579 a h
  have h3 : Entails.eval a c578 := derived578 a h
  have h4 : Entails.eval a c580 := derived580 a h
  have h5 : Entails.eval a c583 := derived583 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c396 := h 395 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨1, by decide⟩, false), (⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c339, some c442, some c18, some c16, some c72, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p585 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 31) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c252, c339, c442, c18, c16, c72] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c442 := h 441 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c58, some c64, some c50, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p586 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 31) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c58, c64, c50] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c579, some c552, some c81, some c586, some c584, some c561, some c585, some c156, some c39, some c35, some c133, some c392, some c50, some c41, some c256, some c320, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p587 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 31) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c579, c552, c81, c586, c584, c561, c585, c156, c39, c35, c133, c392, c50, c41, c256, c320] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c579 := derived579 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c586 := derived586 a h
  have h4 : Entails.eval a c584 := derived584 a h
  have h5 : Entails.eval a c561 := derived561 a h
  have h6 : Entails.eval a c585 := derived585 a h
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c392 := h 391 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c41 := h 40 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c586, some c65, some c84, some c120, some c193, some c128, some c271, some c420, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p588 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 31) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c81, c586, c65, c84, c120, c193, c128, c271, c420] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c586 := derived586 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c128 := h 127 (by decide)
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c420 := h 419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c579, some c552, some c81, some c586, some c587, some c588, some c52, some c129, some c59, some c62, some c166, some c295, some c50, some c175, some c224, some c367, some c464, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p589 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 31) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c579, c552, c81, c586, c587, c588, c52, c129, c59, c62, c166, c295, c50, c175, c224, c367, c464] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c579 := derived579 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c586 := derived586 a h
  have h4 : Entails.eval a c587 := derived587 a h
  have h5 : Entails.eval a c588 := derived588 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c166 := h 165 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c175 := h 174 (by decide)
  have h14 : Entails.eval a c224 := h 223 (by decide)
  have h15 : Entails.eval a c367 := h 366 (by decide)
  have h16 : Entails.eval a c464 := h 463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c311, some c324, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p590 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 31) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c311, c324] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c311 := h 310 (by decide)
  have h1 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c591 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c579, some c84, some c589, some c109, some c552, some c393, some c590, some c121, some c59, some c51, some c515, some c88, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p591 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 31) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c579, c84, c589, c109, c552, c393, c590, c121, c59, c51, c515, c88] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c579 := derived579 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c589 := derived589 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c552 := derived552 a h
  have h5 : Entails.eval a c393 := h 392 (by decide)
  have h6 : Entails.eval a c590 := derived590 a h
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c515 := h 514 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c589, some c103, some c279, some c410, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p592 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 31) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c589, c103, c279, c410] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c279 := h 278 (by decide)
  have h3 : Entails.eval a c410 := h 409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c589, some c109, some c579, some c552, some c84, some c591, some c129, some c35, some c592, some c59, some c166, some c96, some c180, some c521, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p593 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 31) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c589, c109, c579, c552, c84, c591, c129, c35, c592, c59, c166, c96, c180, c521] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c579 := derived579 a h
  have h3 : Entails.eval a c552 := derived552 a h
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c591 := derived591 a h
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c592 := derived592 a h
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c166 := h 165 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c180 := h 179 (by decide)
  have h13 : Entails.eval a c521 := h 520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c508, some c333, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p594 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 31) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c508, c333] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c508 := h 507 (by decide)
  have h1 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c595 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c594, some c180, some c433, some c518, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p595 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 31) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c594, c180, c433, c518] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c594 := derived594 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c433 := h 432 (by decide)
  have h3 : Entails.eval a c518 := h 517 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c593, some c589, some c109, some c579, some c552, some c595, some c392, some c590, some c554, some c575, some c41, some c115, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p596 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 31) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c593, c589, c109, c579, c552, c595, c392, c590, c554, c575, c41, c115] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c593 := derived593 a h
  have h1 : Entails.eval a c589 := derived589 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c579 := derived579 a h
  have h4 : Entails.eval a c552 := derived552 a h
  have h5 : Entails.eval a c595 := derived595 a h
  have h6 : Entails.eval a c392 := h 391 (by decide)
  have h7 : Entails.eval a c590 := derived590 a h
  have h8 : Entails.eval a c554 := derived554 a h
  have h9 : Entails.eval a c575 := derived575 a h
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c593, some c589, some c109, some c579, some c552, some c596, some c65, some c59, some c74, some c51, some c158, some c88, some c433, some c16, some c282, some c354, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p597 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 31) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c593, c589, c109, c579, c552, c596, c65, c59, c74, c51, c158, c88, c433, c16, c282, c354] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c593 := derived593 a h
  have h1 : Entails.eval a c589 := derived589 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c579 := derived579 a h
  have h4 : Entails.eval a c552 := derived552 a h
  have h5 : Entails.eval a c596 := derived596 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c433 := h 432 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c282 := h 281 (by decide)
  have h15 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c65, some c74, some c129, some c158, some c131, some c282, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p598 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 31) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c65, c74, c129, c158, c131, c282] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c589, some c579, some c552, some c109, some c593, some c597, some c598, some c128, some c590, some c41, some c208, some c249, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p599 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 31) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c589, c579, c552, c109, c593, c597, c598, c128, c590, c41, c208, c249] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c579 := derived579 a h
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c593 := derived593 a h
  have h5 : Entails.eval a c597 := derived597 a h
  have h6 : Entails.eval a c598 := derived598 a h
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c590 := derived590 a h
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c120, some c193, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p600 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 31) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c120, c193] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c601 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨28, by decide⟩, true), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c600, some c12, some c222, some c43, some c129, some c208, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p601 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 31) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c600, c12, c222, c43, c129, c208] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c600 := derived600 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c589, some c579, some c552, some c599, some c164, some c601, some c166, some c10, some c277, some c69, some c194, some c12, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p602 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 31) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c589, c579, c552, c599, c164, c601, c166, c10, c277, c69, c194, c12] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c579 := derived579 a h
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c599 := derived599 a h
  have h4 : Entails.eval a c164 := h 163 (by decide)
  have h5 : Entails.eval a c601 := derived601 a h
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c277 := h 276 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c194 := h 193 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c64, some c69, some c101, some c164, some c12, some c194, some c321, some c502, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p603 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 31) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c64, c69, c101, c164, c12, c194, c321, c502] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c64 := h 63 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c321 := h 320 (by decide)
  have h7 : Entails.eval a c502 := h 501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c10, some c180, some c222, some c181, some c24, some c43, some c436, some c208, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p604 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 31) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c10, c180, c222, c181, c24, c43, c436, c208] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c181 := h 180 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c436 := h 435 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c603, some c10, some c604, some c12, some c193, some c83, some c276, some c72, some c70, some c422, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p605 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 31) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c603, c10, c604, c12, c193, c83, c276, c72, c70, c422] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c603 := derived603 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c604 := derived604 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c422 := h 421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c579, some c552, some c589, some c602, some c603, some c605, some c164, some c191, some c72, some c58, some c188, some c18, some c266, some c260, some c285, some c133, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p606 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 31) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c579, c552, c589, c602, c603, c605, c164, c191, c72, c58, c188, c18, c266, c260, c285, c133] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c579 := derived579 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c589 := derived589 a h
  have h3 : Entails.eval a c602 := derived602 a h
  have h4 : Entails.eval a c603 := derived603 a h
  have h5 : Entails.eval a c605 := derived605 a h
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c606, some c552, some c124, some c198, some c579, some c89, some c188, some c249, some c115, some c405, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p607 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 31) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c606, c552, c124, c198, c579, c89, c188, c249, c115, c405] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c579 := derived579 a h
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c405 := h 404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨26, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c50, some c58, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p608 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 31) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c81, c50, c58] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨26, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c606, some c552, some c124, some c198, some c579, some c608, some c89, some c188, some c607, some c115, some c208, some c405, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p609 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 31) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c606, c552, c124, c198, c579, c608, c89, c188, c607, c115, c208, c405] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c579 := derived579 a h
  have h5 : Entails.eval a c608 := derived608 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c607 := derived607 a h
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c405 := h 404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨20, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c159, some c18, some c186, some c227, some c260, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p610 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 31) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c159, c18, c186, c227, c260] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c227 := h 226 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c606, some c552, some c124, some c198, some c579, some c609, some c101, some c610, some c20, some c84, some c75, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p611 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 31) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c606, c552, c124, c198, c579, c609, c101, c610, c20, c84, c75] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c579 := derived579 a h
  have h5 : Entails.eval a c609 := derived609 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c610 := derived610 a h
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c24, some c6, some c18, some c182, some c258, some c223, some c245, some c284, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p612 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 31) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c24, c6, c18, c182, c258, c223, c245, c284] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c258 := h 257 (by decide)
  have h5 : Entails.eval a c223 := h 222 (by decide)
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c552, some c579, some c606, some c124, some c198, some c611, some c16, some c612, some c188, some c205, some c262, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p613 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 31) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c552, c579, c606, c124, c198, c611, c16, c612, c188, c205, c262] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c579 := derived579 a h
  have h2 : Entails.eval a c606 := derived606 a h
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c611 := derived611 a h
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c612 := derived612 a h
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c230, some c188, some c262, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p614 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 31) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c613, c230, c188, c262] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c230 := h 229 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨4, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c552, some c177, some c62, some c166, some c234, some c443, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p615 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 31) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c613, c552, c177, c62, c166, c234, c443] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c234 := h 233 (by decide)
  have h6 : Entails.eval a c443 := h 442 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨4, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c614, some c613, some c615, some c252, some c215, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p616 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 31) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c614, c613, c615, c252, c215] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c614 := derived614 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c615 := derived615 a h
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c614, some c613, some c552, some c118, some c85, some c191, some c89, some c109, some c156, some c263, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p617 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 31) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c614, c613, c552, c118, c85, c191, c89, c109, c156, c263] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c614 := derived614 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c552, some c123, some c150, some c39, some c417, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p618 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 31) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c613, c552, c123, c150, c39, c417] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c417 := h 416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c614, some c616, some c178, some c617, some c618, some c130, some c197, some c238, some c264, some c231, some c452, some c444, some c499, some c214, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p619 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 31) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c613, c614, c616, c178, c617, c618, c130, c197, c238, c264, c231, c452, c444, c499, c214] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c614 := derived614 a h
  have h2 : Entails.eval a c616 := derived616 a h
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c617 := derived617 a h
  have h5 : Entails.eval a c618 := derived618 a h
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c238 := h 237 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c231 := h 230 (by decide)
  have h11 : Entails.eval a c452 := h 451 (by decide)
  have h12 : Entails.eval a c444 := h 443 (by decide)
  have h13 : Entails.eval a c499 := h 498 (by decide)
  have h14 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c619, some c613, some c552, some c178, some c618, some c130, some c197, some c238, some c246, some c343, some c446, some c456, some c264, some c334, some c521, some c511, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p620 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 31) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c619, c613, c552, c178, c618, c130, c197, c238, c246, c343, c446, c456, c264, c334, c521, c511] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c619 := derived619 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c618 := derived618 a h
  have h5 : Entails.eval a c130 := h 129 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c238 := h 237 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c446 := h 445 (by decide)
  have h11 : Entails.eval a c456 := h 455 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c334 := h 333 (by decide)
  have h14 : Entails.eval a c521 := h 520 (by decide)
  have h15 : Entails.eval a c511 := h 510 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨26, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c552, some c456, some c446, some c435, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p621 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 31) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c613, c552, c456, c446, c435] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c456 := h 455 (by decide)
  have h3 : Entails.eval a c446 := h 445 (by decide)
  have h4 : Entails.eval a c435 := h 434 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c166, some c283, some c483, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p622 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 31) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c166, c283, c483] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c166 := h 165 (by decide)
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c483 := h 482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c130, some c619, some c622, some c402, some c24, some c261, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p623 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 31) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c613, c130, c619, c622, c402, c24, c261] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c130 := h 129 (by decide)
  have h2 : Entails.eval a c619 := derived619 a h
  have h3 : Entails.eval a c622 := derived622 a h
  have h4 : Entails.eval a c402 := h 401 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, true), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨4, by decide⟩, false), (⟨26, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c93, some c552, some c196, some c300, some c78, some c104, some c328, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p624 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 31) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c613, c93, c552, c196, c300, c78, c104, c328] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c620, some c619, some c613, some c130, some c197, some c246, some c252, some c621, some c93, some c624, some c622, some c623, some c402, some c191, some c415, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p625 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 31) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c620, c619, c613, c130, c197, c246, c252, c621, c93, c624, c622, c623, c402, c191, c415] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c619 := derived619 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c130 := h 129 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c246 := h 245 (by decide)
  have h6 : Entails.eval a c252 := h 251 (by decide)
  have h7 : Entails.eval a c621 := derived621 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c624 := derived624 a h
  have h10 : Entails.eval a c622 := derived622 a h
  have h11 : Entails.eval a c623 := derived623 a h
  have h12 : Entails.eval a c402 := h 401 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c415 := h 414 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c619, some c613, some c552, some c620, some c625, some c123, some c150, some c39, some c456, some c399, some c624, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p626 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 31) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c619, c613, c552, c620, c625, c123, c150, c39, c456, c399, c624] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c619 := derived619 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c620 := derived620 a h
  have h4 : Entails.eval a c625 := derived625 a h
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c456 := h 455 (by decide)
  have h9 : Entails.eval a c399 := h 398 (by decide)
  have h10 : Entails.eval a c624 := derived624 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c552, some c619, some c626, some c16, some c24, some c6, some c18, some c291, some c182, some c245, some c258, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p627 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 31) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c613, c552, c619, c626, c16, c24, c6, c18, c291, c182, c245, c258] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c619 := derived619 a h
  have h3 : Entails.eval a c626 := derived626 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c291 := h 290 (by decide)
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  have h11 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c627, some c613, some c552, some c614, some c159, some c18, some c24, some c186, some c7, some c260, some c289, some c245, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p628 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 31) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c627, c613, c552, c614, c159, c18, c24, c186, c7, c260, c289, c245] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c614 := derived614 a h
  have h4 : Entails.eval a c159 := h 158 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c260 := h 259 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived628

end CochromaticTwenty.Certificates.Z12Direct_5_8_5
