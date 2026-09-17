import MerLeanExperiment.Certificates.Z12Direct_5_7_13.Inputs

/-! Generated from the actual pinned z12direct_5_7_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c343 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f343 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c63, some c66, some c12, some c178, some c248, some c79, some c102, some c19, some c82, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p343 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked343 : lratChecker f343 p343 = .success := by decide +kernel
theorem unsat343 : Unsatisfiable (PosFin 31) f343 := by
  apply lratCheckerSound f343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p343
  · intro a ha; simp [p343] at ha; subst a; trivial
  · exact checked343
theorem derived343 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c343 := by
  apply localUnsat_implies_entails f343 [c63, c66, c12, c178, c248, c79, c102, c19, c82] c343 unsat343 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c248 := h 247 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c344 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f344 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c67, some c343, some c53, some c54, some c217, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p344 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked344 : lratChecker f344 p344 = .success := by decide +kernel
theorem unsat344 : Unsatisfiable (PosFin 31) f344 := by
  apply lratCheckerSound f344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p344
  · intro a ha; simp [p344] at ha; subst a; trivial
  · exact checked344
theorem derived344 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c344 := by
  apply localUnsat_implies_entails f344 [c67, c343, c53, c54, c217] c344 unsat344 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c343 := derived343 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c345 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f345 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c63, some c344, some c68, some c79, some c77, some c81, some c12, some c181, some c54, some c162, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p345 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked345 : lratChecker f345 p345 = .success := by decide +kernel
theorem unsat345 : Unsatisfiable (PosFin 31) f345 := by
  apply lratCheckerSound f345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p345
  · intro a ha; simp [p345] at ha; subst a; trivial
  · exact checked345
theorem derived345 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c345 := by
  apply localUnsat_implies_entails f345 [c63, c344, c68, c79, c77, c81, c12, c181, c54, c162] c345 unsat345 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c344 := derived344 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c181 := h 180 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c346 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f346 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c63, some c67, some c66, some c61, some c345, some c69, some c82, some c10, some c52, some c53, some c109, some c179, some c264, some c254, some c236, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p346 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked346 : lratChecker f346 p346 = .success := by decide +kernel
theorem unsat346 : Unsatisfiable (PosFin 31) f346 := by
  apply lratCheckerSound f346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p346
  · intro a ha; simp [p346] at ha; subst a; trivial
  · exact checked346
theorem derived346 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c346 := by
  apply localUnsat_implies_entails f346 [c63, c67, c66, c61, c345, c69, c82, c10, c52, c53, c109, c179, c264, c254, c236] c346 unsat346 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c345 := derived345 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c179 := h 178 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c254 := h 253 (by decide)
  have h14 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c347 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f347 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c54, some c177, some c44, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p347 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked347 : lratChecker f347 p347 = .success := by decide +kernel
theorem unsat347 : Unsatisfiable (PosFin 31) f347 := by
  apply lratCheckerSound f347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p347
  · intro a ha; simp [p347] at ha; subst a; trivial
  · exact checked347
theorem derived347 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c347 := by
  apply localUnsat_implies_entails f347 [c54, c177, c44] c347 unsat347 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c177 := h 176 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c348 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f348 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c346, some c63, some c347, some c146, some c179, some c52, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p348 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked348 : lratChecker f348 p348 = .success := by decide +kernel
theorem unsat348 : Unsatisfiable (PosFin 31) f348 := by
  apply lratCheckerSound f348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p348
  · intro a ha; simp [p348] at ha; subst a; trivial
  · exact checked348
theorem derived348 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c348 := by
  apply localUnsat_implies_entails f348 [c346, c63, c347, c146, c179, c52] c348 unsat348 (by rfl) a
  have h0 : Entails.eval a c346 := derived346 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c347 := derived347 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c179 := h 178 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c349 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f349 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c52, some c53, some c46, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p349 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked349 : lratChecker f349 p349 = .success := by decide +kernel
theorem unsat349 : Unsatisfiable (PosFin 31) f349 := by
  apply lratCheckerSound f349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p349
  · intro a ha; simp [p349] at ha; subst a; trivial
  · exact checked349
theorem derived349 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c349 := by
  apply localUnsat_implies_entails f349 [c52, c53, c46] c349 unsat349 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c350 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f350 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c63, some c346, some c348, some c349, some c146, some c288, some c54, some c177, some c289, some c178, some c93, some c10, some c106, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p350 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked350 : lratChecker f350 p350 = .success := by decide +kernel
theorem unsat350 : Unsatisfiable (PosFin 31) f350 := by
  apply lratCheckerSound f350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p350
  · intro a ha; simp [p350] at ha; subst a; trivial
  · exact checked350
theorem derived350 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c350 := by
  apply localUnsat_implies_entails f350 [c63, c346, c348, c349, c146, c288, c54, c177, c289, c178, c93, c10, c106] c350 unsat350 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c346 := derived346 a h
  have h2 : Entails.eval a c348 := derived348 a h
  have h3 : Entails.eval a c349 := derived349 a h
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c351 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f351 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c54, some c176, some c177, some c62, some c147, some c290, some c247, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p351 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked351 : lratChecker f351 p351 = .success := by decide +kernel
theorem unsat351 : Unsatisfiable (PosFin 31) f351 := by
  apply lratCheckerSound f351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p351
  · intro a ha; simp [p351] at ha; subst a; trivial
  · exact checked351
theorem derived351 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c351 := by
  apply localUnsat_implies_entails f351 [c54, c176, c177, c62, c147, c290, c247] c351 unsat351 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c352 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f352 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c350, some c351, some c47, some c52, some c45, some c146, some c62, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p352 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked352 : lratChecker f352 p352 = .success := by decide +kernel
theorem unsat352 : Unsatisfiable (PosFin 31) f352 := by
  apply lratCheckerSound f352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p352
  · intro a ha; simp [p352] at ha; subst a; trivial
  · exact checked352
theorem derived352 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c352 := by
  apply localUnsat_implies_entails f352 [c350, c351, c47, c52, c45, c146, c62] c352 unsat352 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c351 := derived351 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c353 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f353 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c52, some c53, some c147, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p353 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked353 : lratChecker f353 p353 = .success := by decide +kernel
theorem unsat353 : Unsatisfiable (PosFin 31) f353 := by
  apply lratCheckerSound f353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p353
  · intro a ha; simp [p353] at ha; subst a; trivial
  · exact checked353
theorem derived353 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c353 := by
  apply localUnsat_implies_entails f353 [c52, c53, c147] c353 unsat353 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c354 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f354 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c67, some c350, some c352, some c61, some c353, some c45, some c10, some c54, some c82, some c147, some c2, some c19, some c69, some c93, some c215, some c27, some c81, some c223, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p354 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked354 : lratChecker f354 p354 = .success := by decide +kernel
theorem unsat354 : Unsatisfiable (PosFin 31) f354 := by
  apply lratCheckerSound f354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p354
  · intro a ha; simp [p354] at ha; subst a; trivial
  · exact checked354
theorem derived354 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c354 := by
  apply localUnsat_implies_entails f354 [c66, c67, c350, c352, c61, c353, c45, c10, c54, c82, c147, c2, c19, c69, c93, c215, c27, c81, c223] c354 unsat354 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c352 := derived352 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c353 := derived353 a h
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c93 := h 92 (by decide)
  have h15 : Entails.eval a c215 := h 214 (by decide)
  have h16 : Entails.eval a c27 := h 26 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c355 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨16, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f355 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c54, some c215, some c92, some c287, some c104, some c290, some c12, some c247, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p355 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked355 : lratChecker f355 p355 = .success := by decide +kernel
theorem unsat355 : Unsatisfiable (PosFin 31) f355 := by
  apply lratCheckerSound f355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p355
  · intro a ha; simp [p355] at ha; subst a; trivial
  · exact checked355
theorem derived355 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c355 := by
  apply localUnsat_implies_entails f355 [c54, c215, c92, c287, c104, c290, c12, c247] c355 unsat355 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c356 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f356 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c54, some c66, some c216, some c92, some c104, some c12, some c152, some c126, some c32, some c122, some c35, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p356 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked356 : lratChecker f356 p356 = .success := by decide +kernel
theorem unsat356 : Unsatisfiable (PosFin 31) f356 := by
  apply lratCheckerSound f356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p356
  · intro a ha; simp [p356] at ha; subst a; trivial
  · exact checked356
theorem derived356 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c356 := by
  apply localUnsat_implies_entails f356 [c54, c66, c216, c92, c104, c12, c152, c126, c32, c122, c35] c356 unsat356 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c216 := h 215 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c357 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f357 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c54, some c356, some c147, some c355, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p357 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked357 : lratChecker f357 p357 = .success := by decide +kernel
theorem unsat357 : Unsatisfiable (PosFin 31) f357 := by
  apply lratCheckerSound f357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p357
  · intro a ha; simp [p357] at ha; subst a; trivial
  · exact checked357
theorem derived357 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c357 := by
  apply localUnsat_implies_entails f357 [c54, c356, c147, c355] c357 unsat357 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c356 := derived356 a h
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c355 := derived355 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c358 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f358 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c215, some c45, some c287, some c56, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p358 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked358 : lratChecker f358 p358 = .success := by decide +kernel
theorem unsat358 : Unsatisfiable (PosFin 31) f358 := by
  apply lratCheckerSound f358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p358
  · intro a ha; simp [p358] at ha; subst a; trivial
  · exact checked358
theorem derived358 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c358 := by
  apply localUnsat_implies_entails f358 [c215, c45, c287, c56] c358 unsat358 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c287 := h 286 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c359 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f359 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c22, some c105, some c80, some c12, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p359 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked359 : lratChecker f359 p359 = .success := by decide +kernel
theorem unsat359 : Unsatisfiable (PosFin 31) f359 := by
  apply lratCheckerSound f359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p359
  · intro a ha; simp [p359] at ha; subst a; trivial
  · exact checked359
theorem derived359 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c359 := by
  apply localUnsat_implies_entails f359 [c22, c105, c80, c12] c359 unsat359 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c360 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f360 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c354, some c66, some c357, some c13, some c359, some c1, some c92, some c68, some c20, some c133, some c284, some c83, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p360 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked360 : lratChecker f360 p360 = .success := by decide +kernel
theorem unsat360 : Unsatisfiable (PosFin 31) f360 := by
  apply lratCheckerSound f360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p360
  · intro a ha; simp [p360] at ha; subst a; trivial
  · exact checked360
theorem derived360 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c360 := by
  apply localUnsat_implies_entails f360 [c354, c66, c357, c13, c359, c1, c92, c68, c20, c133, c284, c83] c360 unsat360 (by rfl) a
  have h0 : Entails.eval a c354 := derived354 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c357 := derived357 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c359 := derived359 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c361 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f361 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c360, some c354, some c66, some c13, some c47, some c359, some c1, some c68, some c20, some c133, some c285, some c106, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p361 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked361 : lratChecker f361 p361 = .success := by decide +kernel
theorem unsat361 : Unsatisfiable (PosFin 31) f361 := by
  apply lratCheckerSound f361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p361
  · intro a ha; simp [p361] at ha; subst a; trivial
  · exact checked361
theorem derived361 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c361 := by
  apply localUnsat_implies_entails f361 [c360, c354, c66, c13, c47, c359, c1, c68, c20, c133, c285, c106] c361 unsat361 (by rfl) a
  have h0 : Entails.eval a c360 := derived360 a h
  have h1 : Entails.eval a c354 := derived354 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c359 := derived359 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c285 := h 284 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c362 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f362 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c1, some c68, some c20, some c19, some c314, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p362 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked362 : lratChecker f362 p362 = .success := by decide +kernel
theorem unsat362 : Unsatisfiable (PosFin 31) f362 := by
  apply lratCheckerSound f362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p362
  · intro a ha; simp [p362] at ha; subst a; trivial
  · exact checked362
theorem derived362 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c362 := by
  apply localUnsat_implies_entails f362 [c66, c1, c68, c20, c19, c314] c362 unsat362 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c363 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f363 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c354, some c66, some c360, some c361, some c54, some c176, some c177, some c51, some c362, some c104, some c80, some c190, some c305, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p363 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked363 : lratChecker f363 p363 = .success := by decide +kernel
theorem unsat363 : Unsatisfiable (PosFin 31) f363 := by
  apply lratCheckerSound f363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p363
  · intro a ha; simp [p363] at ha; subst a; trivial
  · exact checked363
theorem derived363 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c363 := by
  apply localUnsat_implies_entails f363 [c354, c66, c360, c361, c54, c176, c177, c51, c362, c104, c80, c190, c305] c363 unsat363 (by rfl) a
  have h0 : Entails.eval a c354 := derived354 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c360 := derived360 a h
  have h3 : Entails.eval a c361 := derived361 a h
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c177 := h 176 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c362 := derived362 a h
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c364 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f364 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c363, some c63, some c354, some c66, some c54, some c12, some c79, some c92, some c20, some c362, some c114, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p364 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked364 : lratChecker f364 p364 = .success := by decide +kernel
theorem unsat364 : Unsatisfiable (PosFin 31) f364 := by
  apply lratCheckerSound f364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p364
  · intro a ha; simp [p364] at ha; subst a; trivial
  · exact checked364
theorem derived364 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c364 := by
  apply localUnsat_implies_entails f364 [c363, c63, c354, c66, c54, c12, c79, c92, c20, c362, c114] c364 unsat364 (by rfl) a
  have h0 : Entails.eval a c363 := derived363 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c354 := derived354 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c362 := derived362 a h
  have h10 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c365 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f365 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c363, some c63, some c354, some c66, some c1, some c92, some c68, some c20, some c313, some c19, some c273, some c86, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p365 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked365 : lratChecker f365 p365 = .success := by decide +kernel
theorem unsat365 : Unsatisfiable (PosFin 31) f365 := by
  apply lratCheckerSound f365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p365
  · intro a ha; simp [p365] at ha; subst a; trivial
  · exact checked365
theorem derived365 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c365 := by
  apply localUnsat_implies_entails f365 [c363, c63, c354, c66, c1, c92, c68, c20, c313, c19, c273, c86] c365 unsat365 (by rfl) a
  have h0 : Entails.eval a c363 := derived363 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c354 := derived354 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c273 := h 272 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c366 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f366 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c363, some c63, some c365, some c79, some c12, some c359, some c364, some c354, some c66, some c60, some c179, some c89, some c17, some c245, some c103, some c110, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p366 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked366 : lratChecker f366 p366 = .success := by decide +kernel
theorem unsat366 : Unsatisfiable (PosFin 31) f366 := by
  apply lratCheckerSound f366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p366
  · intro a ha; simp [p366] at ha; subst a; trivial
  · exact checked366
theorem derived366 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c366 := by
  apply localUnsat_implies_entails f366 [c363, c63, c365, c79, c12, c359, c364, c354, c66, c60, c179, c89, c17, c245, c103, c110] c366 unsat366 (by rfl) a
  have h0 : Entails.eval a c363 := derived363 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c365 := derived365 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c359 := derived359 a h
  have h6 : Entails.eval a c364 := derived364 a h
  have h7 : Entails.eval a c354 := derived354 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c245 := h 244 (by decide)
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c367 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨26, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f367 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c12, some c359, some c179, some c15, some c198, some c281, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p367 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked367 : lratChecker f367 p367 = .success := by decide +kernel
theorem unsat367 : Unsatisfiable (PosFin 31) f367 := by
  apply lratCheckerSound f367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p367
  · intro a ha; simp [p367] at ha; subst a; trivial
  · exact checked367
theorem derived367 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c367 := by
  apply localUnsat_implies_entails f367 [c12, c359, c179, c15, c198, c281] c367 unsat367 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c359 := derived359 a h
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c368 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f368 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c354, some c363, some c63, some c364, some c365, some c79, some c359, some c12, some c366, some c367, some c274, some c260, some c229, some c208, some c204, some c181, some c89, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p368 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked368 : lratChecker f368 p368 = .success := by decide +kernel
theorem unsat368 : Unsatisfiable (PosFin 31) f368 := by
  apply lratCheckerSound f368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p368
  · intro a ha; simp [p368] at ha; subst a; trivial
  · exact checked368
theorem derived368 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c368 := by
  apply localUnsat_implies_entails f368 [c66, c354, c363, c63, c364, c365, c79, c359, c12, c366, c367, c274, c260, c229, c208, c204, c181, c89] c368 unsat368 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c354 := derived354 a h
  have h2 : Entails.eval a c363 := derived363 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c364 := derived364 a h
  have h5 : Entails.eval a c365 := derived365 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c359 := derived359 a h
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c366 := derived366 a h
  have h10 : Entails.eval a c367 := derived367 a h
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c260 := h 259 (by decide)
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c204 := h 203 (by decide)
  have h16 : Entails.eval a c181 := h 180 (by decide)
  have h17 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c369 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f369 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c12, some c367, some c274, some c163, some c229, some c4, some c98, some c205, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p369 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked369 : lratChecker f369 p369 = .success := by decide +kernel
theorem unsat369 : Unsatisfiable (PosFin 31) f369 := by
  apply lratCheckerSound f369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p369
  · intro a ha; simp [p369] at ha; subst a; trivial
  · exact checked369
theorem derived369 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c369 := by
  apply localUnsat_implies_entails f369 [c12, c367, c274, c163, c229, c4, c98, c205] c369 unsat369 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c367 := derived367 a h
  have h2 : Entails.eval a c274 := h 273 (by decide)
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c229 := h 228 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c370 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f370 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c60, some c179, some c194, some c197, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p370 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked370 : lratChecker f370 p370 = .success := by decide +kernel
theorem unsat370 : Unsatisfiable (PosFin 31) f370 := by
  apply lratCheckerSound f370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p370
  · intro a ha; simp [p370] at ha; subst a; trivial
  · exact checked370
theorem derived370 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c370 := by
  apply localUnsat_implies_entails f370 [c60, c179, c194, c197] c370 unsat370 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c371 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f371 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c63, some c368, some c66, some c79, some c359, some c12, some c54, some c370, some c367, some c369, some c274, some c53, some c163, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p371 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked371 : lratChecker f371 p371 = .success := by decide +kernel
theorem unsat371 : Unsatisfiable (PosFin 31) f371 := by
  apply lratCheckerSound f371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p371
  · intro a ha; simp [p371] at ha; subst a; trivial
  · exact checked371
theorem derived371 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c371 := by
  apply localUnsat_implies_entails f371 [c63, c368, c66, c79, c359, c12, c54, c370, c367, c369, c274, c53, c163] c371 unsat371 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c368 := derived368 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c359 := derived359 a h
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c370 := derived370 a h
  have h8 : Entails.eval a c367 := derived367 a h
  have h9 : Entails.eval a c369 := derived369 a h
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c372 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f372 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c371, some c68, some c66, some c1, some c30, some c92, some c24, some c29, some c153, some c240, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p372 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked372 : lratChecker f372 p372 = .success := by decide +kernel
theorem unsat372 : Unsatisfiable (PosFin 31) f372 := by
  apply lratCheckerSound f372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p372
  · intro a ha; simp [p372] at ha; subst a; trivial
  · exact checked372
theorem derived372 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c372 := by
  apply localUnsat_implies_entails f372 [c371, c68, c66, c1, c30, c92, c24, c29, c153, c240] c372 unsat372 (by rfl) a
  have h0 : Entails.eval a c371 := derived371 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c373 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f373 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c371, some c1, some c68, some c30, some c372, some c157, some c229, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p373 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked373 : lratChecker f373 p373 = .success := by decide +kernel
theorem unsat373 : Unsatisfiable (PosFin 31) f373 := by
  apply lratCheckerSound f373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p373
  · intro a ha; simp [p373] at ha; subst a; trivial
  · exact checked373
theorem derived373 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c373 := by
  apply localUnsat_implies_entails f373 [c66, c371, c1, c68, c30, c372, c157, c229] c373 unsat373 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c371 := derived371 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c372 := derived372 a h
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c374 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f374 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c229, some c4, some c26, some c23, some c209, some c173, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p374 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked374 : lratChecker f374 p374 = .success := by decide +kernel
theorem unsat374 : Unsatisfiable (PosFin 31) f374 := by
  apply lratCheckerSound f374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p374
  · intro a ha; simp [p374] at ha; subst a; trivial
  · exact checked374
theorem derived374 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c374 := by
  apply localUnsat_implies_entails f374 [c229, c4, c26, c23, c209, c173] c374 unsat374 (by rfl) a
  have h0 : Entails.eval a c229 := h 228 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c209 := h 208 (by decide)
  have h5 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c375 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f375 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c68, some c92, some c66, some c1, some c373, some c368, some c20, some c374, some c24, some c29, some c47, some c11, some c242, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p375 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked375 : lratChecker f375 p375 = .success := by decide +kernel
theorem unsat375 : Unsatisfiable (PosFin 31) f375 := by
  apply lratCheckerSound f375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p375
  · intro a ha; simp [p375] at ha; subst a; trivial
  · exact checked375
theorem derived375 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c375 := by
  apply localUnsat_implies_entails f375 [c68, c92, c66, c1, c373, c368, c20, c374, c24, c29, c47, c11, c242] c375 unsat375 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c373 := derived373 a h
  have h5 : Entails.eval a c368 := derived368 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c374 := derived374 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c376 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f376 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c68, some c92, some c66, some c1, some c373, some c24, some c29, some c351, some c47, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p376 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked376 : lratChecker f376 p376 = .success := by decide +kernel
theorem unsat376 : Unsatisfiable (PosFin 31) f376 := by
  apply lratCheckerSound f376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p376
  · intro a ha; simp [p376] at ha; subst a; trivial
  · exact checked376
theorem derived376 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c376 := by
  apply localUnsat_implies_entails f376 [c375, c68, c92, c66, c1, c373, c24, c29, c351, c47] c376 unsat376 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c373 := derived373 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c351 := derived351 a h
  have h9 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c377 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f377 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c1, some c375, some c376, some c157, some c296, some c40, some c260, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p377 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked377 : lratChecker f377 p377 = .success := by decide +kernel
theorem unsat377 : Unsatisfiable (PosFin 31) f377 := by
  apply lratCheckerSound f377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p377
  · intro a ha; simp [p377] at ha; subst a; trivial
  · exact checked377
theorem derived377 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c377 := by
  apply localUnsat_implies_entails f377 [c66, c1, c375, c376, c157, c296, c40, c260] c377 unsat377 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c375 := derived375 a h
  have h3 : Entails.eval a c376 := derived376 a h
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c296 := h 295 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c378 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f378 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c373, some c377, some c359, some c13, some c54, some c147, some c355, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p378 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked378 : lratChecker f378 p378 = .success := by decide +kernel
theorem unsat378 : Unsatisfiable (PosFin 31) f378 := by
  apply lratCheckerSound f378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p378
  · intro a ha; simp [p378] at ha; subst a; trivial
  · exact checked378
theorem derived378 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c378 := by
  apply localUnsat_implies_entails f378 [c373, c377, c359, c13, c54, c147, c355] c378 unsat378 (by rfl) a
  have h0 : Entails.eval a c373 := derived373 a h
  have h1 : Entails.eval a c377 := derived377 a h
  have h2 : Entails.eval a c359 := derived359 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c355 := derived355 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c379 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f379 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c373, some c377, some c359, some c13, some c54, some c104, some c12, some c378, some c62, some c357, some c160, some c18, some c241, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p379 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked379 : lratChecker f379 p379 = .success := by decide +kernel
theorem unsat379 : Unsatisfiable (PosFin 31) f379 := by
  apply lratCheckerSound f379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p379
  · intro a ha; simp [p379] at ha; subst a; trivial
  · exact checked379
theorem derived379 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c379 := by
  apply localUnsat_implies_entails f379 [c373, c377, c359, c13, c54, c104, c12, c378, c62, c357, c160, c18, c241] c379 unsat379 (by rfl) a
  have h0 : Entails.eval a c373 := derived373 a h
  have h1 : Entails.eval a c377 := derived377 a h
  have h2 : Entails.eval a c359 := derived359 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c378 := derived378 a h
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c357 := derived357 a h
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c380 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨21, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f380 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c104, some c5, some c95, some c32, some c126, some c122, some c35, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p380 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked380 : lratChecker f380 p380 = .success := by decide +kernel
theorem unsat380 : Unsatisfiable (PosFin 31) f380 := by
  apply lratCheckerSound f380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p380
  · intro a ha; simp [p380] at ha; subst a; trivial
  · exact checked380
theorem derived380 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c380 := by
  apply localUnsat_implies_entails f380 [c379, c104, c5, c95, c32, c126, c122, c35] c380 unsat380 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c381 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨21, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f381 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c5, some c100, some c32, some c136, some c231, some c155, some c161, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p381 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked381 : lratChecker f381 p381 = .success := by decide +kernel
theorem unsat381 : Unsatisfiable (PosFin 31) f381 := by
  apply lratCheckerSound f381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p381
  · intro a ha; simp [p381] at ha; subst a; trivial
  · exact checked381
theorem derived381 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c381 := by
  apply localUnsat_implies_entails f381 [c5, c100, c32, c136, c231, c155, c161] c381 unsat381 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c231 := h 230 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c382 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, true), (⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f382 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c3, some c151, some c171, some c231, some c237, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p382 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked382 : lratChecker f382 p382 = .success := by decide +kernel
theorem unsat382 : Unsatisfiable (PosFin 31) f382 := by
  apply lratCheckerSound f382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p382
  · intro a ha; simp [p382] at ha; subst a; trivial
  · exact checked382
theorem derived382 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c382 := by
  apply localUnsat_implies_entails f382 [c3, c151, c171, c231, c237] c382 unsat382 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c231 := h 230 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c383 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f383 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c3, some c379, some c176, some c231, some c51, some c113, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p383 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked383 : lratChecker f383 p383 = .success := by decide +kernel
theorem unsat383 : Unsatisfiable (PosFin 31) f383 := by
  apply lratCheckerSound f383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p383
  · intro a ha; simp [p383] at ha; subst a; trivial
  · exact checked383
theorem derived383 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c383 := by
  apply localUnsat_implies_entails f383 [c3, c379, c176, c231, c51, c113] c383 unsat383 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c379 := derived379 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c231 := h 230 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c384 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨21, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f384 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c380, some c381, some c3, some c382, some c169, some c23, some c383, some c65, some c171, some c196, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p384 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked384 : lratChecker f384 p384 = .success := by decide +kernel
theorem unsat384 : Unsatisfiable (PosFin 31) f384 := by
  apply lratCheckerSound f384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p384
  · intro a ha; simp [p384] at ha; subst a; trivial
  · exact checked384
theorem derived384 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c384 := by
  apply localUnsat_implies_entails f384 [c379, c380, c381, c3, c382, c169, c23, c383, c65, c171, c196] c384 unsat384 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c380 := derived380 a h
  have h2 : Entails.eval a c381 := derived381 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c382 := derived382 a h
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c383 := derived383 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c171 := h 170 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c385 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f385 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c380, some c384, some c311, some c32, some c129, some c151, some c227, some c41, some c328, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p385 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked385 : lratChecker f385 p385 = .success := by decide +kernel
theorem unsat385 : Unsatisfiable (PosFin 31) f385 := by
  apply lratCheckerSound f385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p385
  · intro a ha; simp [p385] at ha; subst a; trivial
  · exact checked385
theorem derived385 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c385 := by
  apply localUnsat_implies_entails f385 [c380, c384, c311, c32, c129, c151, c227, c41, c328] c385 unsat385 (by rfl) a
  have h0 : Entails.eval a c380 := derived380 a h
  have h1 : Entails.eval a c384 := derived384 a h
  have h2 : Entails.eval a c311 := h 310 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c227 := h 226 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c386 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f386 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c385, some c147, some c215, some c287, some c290, some c247, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p386 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked386 : lratChecker f386 p386 = .success := by decide +kernel
theorem unsat386 : Unsatisfiable (PosFin 31) f386 := by
  apply lratCheckerSound f386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p386
  · intro a ha; simp [p386] at ha; subst a; trivial
  · exact checked386
theorem derived386 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c386 := by
  apply localUnsat_implies_entails f386 [c385, c147, c215, c287, c290, c247] c386 unsat386 (by rfl) a
  have h0 : Entails.eval a c385 := derived385 a h
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c387 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨26, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f387 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c263, some c242, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p387 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked387 : lratChecker f387 p387 = .success := by decide +kernel
theorem unsat387 : Unsatisfiable (PosFin 31) f387 := by
  apply lratCheckerSound f387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p387
  · intro a ha; simp [p387] at ha; subst a; trivial
  · exact checked387
theorem derived387 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c387 := by
  apply localUnsat_implies_entails f387 [c379, c263, c242] c387 unsat387 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c388 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f388 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c287, some c51, some c290, some c247, some c318, some c10, some c387, some c321, some c78, some c104, some c88, some c265, some c286, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p388 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked388 : lratChecker f388 p388 = .success := by decide +kernel
theorem unsat388 : Unsatisfiable (PosFin 31) f388 := by
  apply lratCheckerSound f388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p388
  · intro a ha; simp [p388] at ha; subst a; trivial
  · exact checked388
theorem derived388 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c388 := by
  apply localUnsat_implies_entails f388 [c379, c287, c51, c290, c247, c318, c10, c387, c321, c78, c104, c88, c265, c286] c388 unsat388 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c287 := h 286 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c290 := h 289 (by decide)
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c387 := derived387 a h
  have h8 : Entails.eval a c321 := h 320 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c389 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f389 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c386, some c55, some c388, some c149, some c214, some c145, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p389 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked389 : lratChecker f389 p389 = .success := by decide +kernel
theorem unsat389 : Unsatisfiable (PosFin 31) f389 := by
  apply lratCheckerSound f389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p389
  · intro a ha; simp [p389] at ha; subst a; trivial
  · exact checked389
theorem derived389 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c389 := by
  apply localUnsat_implies_entails f389 [c386, c55, c388, c149, c214, c145] c389 unsat389 (by rfl) a
  have h0 : Entails.eval a c386 := derived386 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c388 := derived388 a h
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c214 := h 213 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c390 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f390 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c177, some c176, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p390 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked390 : lratChecker f390 p390 = .success := by decide +kernel
theorem unsat390 : Unsatisfiable (PosFin 31) f390 := by
  apply lratCheckerSound f390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p390
  · intro a ha; simp [p390] at ha; subst a; trivial
  · exact checked390
theorem derived390 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c390 := by
  apply localUnsat_implies_entails f390 [c177, c176] c390 unsat390 (by rfl) a
  have h0 : Entails.eval a c177 := h 176 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c391 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f391 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c389, some c12, some c104, some c390, some c216, some c65, some c221, some c8, some c44, some c330, some c308, some c314, some c311, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p391 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked391 : lratChecker f391 p391 = .success := by decide +kernel
theorem unsat391 : Unsatisfiable (PosFin 31) f391 := by
  apply lratCheckerSound f391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p391
  · intro a ha; simp [p391] at ha; subst a; trivial
  · exact checked391
theorem derived391 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c391 := by
  apply localUnsat_implies_entails f391 [c389, c12, c104, c390, c216, c65, c221, c8, c44, c330, c308, c314, c311] c391 unsat391 (by rfl) a
  have h0 : Entails.eval a c389 := derived389 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c390 := derived390 a h
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c330 := h 329 (by decide)
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c392 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f392 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c389, some c391, some c55, some c149, some c177, some c244, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p392 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked392 : lratChecker f392 p392 = .success := by decide +kernel
theorem unsat392 : Unsatisfiable (PosFin 31) f392 := by
  apply lratCheckerSound f392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p392
  · intro a ha; simp [p392] at ha; subst a; trivial
  · exact checked392
theorem derived392 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c392 := by
  apply localUnsat_implies_entails f392 [c389, c391, c55, c149, c177, c244] c392 unsat392 (by rfl) a
  have h0 : Entails.eval a c389 := derived389 a h
  have h1 : Entails.eval a c391 := derived391 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c177 := h 176 (by decide)
  have h5 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c393 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f393 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c389, some c392, some c55, some c287, some c177, some c180, some c51, some c97, some c300, some c330, some c297, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p393 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked393 : lratChecker f393 p393 = .success := by decide +kernel
theorem unsat393 : Unsatisfiable (PosFin 31) f393 := by
  apply lratCheckerSound f393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p393
  · intro a ha; simp [p393] at ha; subst a; trivial
  · exact checked393
theorem derived393 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c393 := by
  apply localUnsat_implies_entails f393 [c389, c392, c55, c287, c177, c180, c51, c97, c300, c330, c297] c393 unsat393 (by rfl) a
  have h0 : Entails.eval a c389 := derived389 a h
  have h1 : Entails.eval a c392 := derived392 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c177 := h 176 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c300 := h 299 (by decide)
  have h9 : Entails.eval a c330 := h 329 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c394 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f394 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c392, some c389, some c379, some c55, some c287, some c177, some c51, some c290, some c180, some c316, some c56, some c393, some c78, some c104, some c88, some c263, some c286, some c131, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p394 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked394 : lratChecker f394 p394 = .success := by decide +kernel
theorem unsat394 : Unsatisfiable (PosFin 31) f394 := by
  apply lratCheckerSound f394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p394
  · intro a ha; simp [p394] at ha; subst a; trivial
  · exact checked394
theorem derived394 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c394 := by
  apply localUnsat_implies_entails f394 [c392, c389, c379, c55, c287, c177, c51, c290, c180, c316, c56, c393, c78, c104, c88, c263, c286, c131] c394 unsat394 (by rfl) a
  have h0 : Entails.eval a c392 := derived392 a h
  have h1 : Entails.eval a c389 := derived389 a h
  have h2 : Entails.eval a c379 := derived379 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c287 := h 286 (by decide)
  have h5 : Entails.eval a c177 := h 176 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c393 := derived393 a h
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c286 := h 285 (by decide)
  have h17 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c395 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f395 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c389, some c392, some c394, some c12, some c147, some c104, some c215, some c287, some c51, some c99, some c300, some c115, some c307, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p395 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked395 : lratChecker f395 p395 = .success := by decide +kernel
theorem unsat395 : Unsatisfiable (PosFin 31) f395 := by
  apply lratCheckerSound f395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p395
  · intro a ha; simp [p395] at ha; subst a; trivial
  · exact checked395
theorem derived395 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c395 := by
  apply localUnsat_implies_entails f395 [c389, c392, c394, c12, c147, c104, c215, c287, c51, c99, c300, c115, c307] c395 unsat395 (by rfl) a
  have h0 : Entails.eval a c389 := derived389 a h
  have h1 : Entails.eval a c392 := derived392 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c287 := h 286 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c300 := h 299 (by decide)
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c396 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨20, by decide⟩, false), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f396 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c70, some c87, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p396 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked396 : lratChecker f396 p396 = .success := by decide +kernel
theorem unsat396 : Unsatisfiable (PosFin 31) f396 := by
  apply lratCheckerSound f396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p396
  · intro a ha; simp [p396] at ha; subst a; trivial
  · exact checked396
theorem derived396 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c396 := by
  apply localUnsat_implies_entails f396 [c70, c87] c396 unsat396 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c397 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f397 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c395, some c358, some c218, some c147, some c47, some c45, some c13, some c379, some c179, some c246, some c73, some c287, some c396, some c91, some c338, some c334, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p397 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked397 : lratChecker f397 p397 = .success := by decide +kernel
theorem unsat397 : Unsatisfiable (PosFin 31) f397 := by
  apply lratCheckerSound f397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p397
  · intro a ha; simp [p397] at ha; subst a; trivial
  · exact checked397
theorem derived397 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c397 := by
  apply localUnsat_implies_entails f397 [c395, c358, c218, c147, c47, c45, c13, c379, c179, c246, c73, c287, c396, c91, c338, c334] c397 unsat397 (by rfl) a
  have h0 : Entails.eval a c395 := derived395 a h
  have h1 : Entails.eval a c358 := derived358 a h
  have h2 : Entails.eval a c218 := h 217 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c379 := derived379 a h
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c396 := derived396 a h
  have h13 : Entails.eval a c91 := h 90 (by decide)
  have h14 : Entails.eval a c338 := h 337 (by decide)
  have h15 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c398 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨13, by decide⟩, false), (⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f398 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c126, some c25, some c1, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p398 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked398 : lratChecker f398 p398 = .success := by decide +kernel
theorem unsat398 : Unsatisfiable (PosFin 31) f398 := by
  apply lratCheckerSound f398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p398
  · intro a ha; simp [p398] at ha; subst a; trivial
  · exact checked398
theorem derived398 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c398 := by
  apply localUnsat_implies_entails f398 [c126, c25, c1] c398 unsat398 (by rfl) a
  have h0 : Entails.eval a c126 := h 125 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c399 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f399 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c358, some c206, some c159, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p399 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked399 : lratChecker f399 p399 = .success := by decide +kernel
theorem unsat399 : Unsatisfiable (PosFin 31) f399 := by
  apply lratCheckerSound f399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p399
  · intro a ha; simp [p399] at ha; subst a; trivial
  · exact checked399
theorem derived399 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c399 := by
  apply localUnsat_implies_entails f399 [c358, c206, c159] c399 unsat399 (by rfl) a
  have h0 : Entails.eval a c358 := derived358 a h
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c400 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f400 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c395, some c13, some c379, some c45, some c358, some c47, some c147, some c218, some c397, some c318, some c287, some c246, some c9, some c399, some c166, some c341, some c398, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p400 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked400 : lratChecker f400 p400 = .success := by decide +kernel
theorem unsat400 : Unsatisfiable (PosFin 31) f400 := by
  apply lratCheckerSound f400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p400
  · intro a ha; simp [p400] at ha; subst a; trivial
  · exact checked400
theorem derived400 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c400 := by
  apply localUnsat_implies_entails f400 [c395, c13, c379, c45, c358, c47, c147, c218, c397, c318, c287, c246, c9, c399, c166, c341, c398] c400 unsat400 (by rfl) a
  have h0 : Entails.eval a c395 := derived395 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c379 := derived379 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c358 := derived358 a h
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c397 := derived397 a h
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c287 := h 286 (by decide)
  have h11 : Entails.eval a c246 := h 245 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c399 := derived399 a h
  have h14 : Entails.eval a c166 := h 165 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  have h16 : Entails.eval a c398 := derived398 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c401 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨25, by decide⟩, true), (⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f401 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c398, some c5, some c22, some c144, some c1, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p401 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked401 : lratChecker f401 p401 = .success := by decide +kernel
theorem unsat401 : Unsatisfiable (PosFin 31) f401 := by
  apply lratCheckerSound f401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p401
  · intro a ha; simp [p401] at ha; subst a; trivial
  · exact checked401
theorem derived401 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c401 := by
  apply localUnsat_implies_entails f401 [c398, c5, c22, c144, c1] c401 unsat401 (by rfl) a
  have h0 : Entails.eval a c398 := derived398 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c402 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f402 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c148, some c315, some c56, some c247, some c214, some c291, some c65, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p402 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked402 : lratChecker f402 p402 = .success := by decide +kernel
theorem unsat402 : Unsatisfiable (PosFin 31) f402 := by
  apply lratCheckerSound f402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p402
  · intro a ha; simp [p402] at ha; subst a; trivial
  · exact checked402
theorem derived402 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c402 := by
  apply localUnsat_implies_entails f402 [c148, c315, c56, c247, c214, c291, c65] c402 unsat402 (by rfl) a
  have h0 : Entails.eval a c148 := h 147 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c247 := h 246 (by decide)
  have h4 : Entails.eval a c214 := h 213 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c403 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f403 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c13, some c148, some c402, some c401, some c48, some c118, some c21, some c5, some c283, some c32, some c126, some c312, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p403 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked403 : lratChecker f403 p403 = .success := by decide +kernel
theorem unsat403 : Unsatisfiable (PosFin 31) f403 := by
  apply lratCheckerSound f403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p403
  · intro a ha; simp [p403] at ha; subst a; trivial
  · exact checked403
theorem derived403 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c403 := by
  apply localUnsat_implies_entails f403 [c13, c148, c402, c401, c48, c118, c21, c5, c283, c32, c126, c312] c403 unsat403 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c402 := derived402 a h
  have h3 : Entails.eval a c401 := derived401 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  have h11 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c404 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, true), (⟨6, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f404 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c70, some c22, some c90, some c118, some c8, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p404 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked404 : lratChecker f404 p404 = .success := by decide +kernel
theorem unsat404 : Unsatisfiable (PosFin 31) f404 := by
  apply lratCheckerSound f404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p404
  · intro a ha; simp [p404] at ha; subst a; trivial
  · exact checked404
theorem derived404 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c404 := by
  apply localUnsat_implies_entails f404 [c70, c22, c90, c118, c8] c404 unsat404 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c405 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f405 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c22, some c8, some c1, some c133, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p405 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked405 : lratChecker f405 p405 = .success := by decide +kernel
theorem unsat405 : Unsatisfiable (PosFin 31) f405 := by
  apply lratCheckerSound f405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p405
  · intro a ha; simp [p405] at ha; subst a; trivial
  · exact checked405
theorem derived405 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c405 := by
  apply localUnsat_implies_entails f405 [c22, c8, c1, c133] c405 unsat405 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c406 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨23, by decide⟩, true), (⟨17, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f406 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c405, some c5, some c140, some c335, some c136, some c179, some c276, some c229, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p406 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked406 : lratChecker f406 p406 = .success := by decide +kernel
theorem unsat406 : Unsatisfiable (PosFin 31) f406 := by
  apply lratCheckerSound f406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p406
  · intro a ha; simp [p406] at ha; subst a; trivial
  · exact checked406
theorem derived406 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c406 := by
  apply localUnsat_implies_entails f406 [c405, c5, c140, c335, c136, c179, c276, c229] c406 unsat406 (by rfl) a
  have h0 : Entails.eval a c405 := derived405 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c407 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨17, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f407 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c406, some c317, some c179, some c245, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p407 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked407 : lratChecker f407 p407 = .success := by decide +kernel
theorem unsat407 : Unsatisfiable (PosFin 31) f407 := by
  apply lratCheckerSound f407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p407
  · intro a ha; simp [p407] at ha; subst a; trivial
  · exact checked407
theorem derived407 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c407 := by
  apply localUnsat_implies_entails f407 [c406, c317, c179, c245] c407 unsat407 (by rfl) a
  have h0 : Entails.eval a c406 := derived406 a h
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c408 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f408 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c400, some c395, some c13, some c379, some c403, some c404, some c407, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p408 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked408 : lratChecker f408 p408 = .success := by decide +kernel
theorem unsat408 : Unsatisfiable (PosFin 31) f408 := by
  apply lratCheckerSound f408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p408
  · intro a ha; simp [p408] at ha; subst a; trivial
  · exact checked408
theorem derived408 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c408 := by
  apply localUnsat_implies_entails f408 [c400, c395, c13, c379, c403, c404, c407] c408 unsat408 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c395 := derived395 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c403 := derived403 a h
  have h5 : Entails.eval a c404 := derived404 a h
  have h6 : Entails.eval a c407 := derived407 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c409 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f409 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c404, some c12, some c22, some c405, some c144, some c1, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p409 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked409 : lratChecker f409 p409 = .success := by decide +kernel
theorem unsat409 : Unsatisfiable (PosFin 31) f409 := by
  apply lratCheckerSound f409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p409
  · intro a ha; simp [p409] at ha; subst a; trivial
  · exact checked409
theorem derived409 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c409 := by
  apply localUnsat_implies_entails f409 [c404, c12, c22, c405, c144, c1] c409 unsat409 (by rfl) a
  have h0 : Entails.eval a c404 := derived404 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c405 := derived405 a h
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c410 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f410 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c22, some c144, some c1, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p410 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked410 : lratChecker f410 p410 = .success := by decide +kernel
theorem unsat410 : Unsatisfiable (PosFin 31) f410 := by
  apply lratCheckerSound f410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p410
  · intro a ha; simp [p410] at ha; subst a; trivial
  · exact checked410
theorem derived410 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c410 := by
  apply localUnsat_implies_entails f410 [c22, c144, c1] c410 unsat410 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c411 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f411 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c13, some c5, some c32, some c126, some c3, some c175, some c312, some c23, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p411 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked411 : lratChecker f411 p411 = .success := by decide +kernel
theorem unsat411 : Unsatisfiable (PosFin 31) f411 := by
  apply lratCheckerSound f411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p411
  · intro a ha; simp [p411] at ha; subst a; trivial
  · exact checked411
theorem derived411 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c411 := by
  apply localUnsat_implies_entails f411 [c13, c5, c32, c126, c3, c175, c312, c23] c411 unsat411 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c412 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f412 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c118, some c410, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p412 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked412 : lratChecker f412 p412 = .success := by decide +kernel
theorem unsat412 : Unsatisfiable (PosFin 31) f412 := by
  apply lratCheckerSound f412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p412
  · intro a ha; simp [p412] at ha; subst a; trivial
  · exact checked412
theorem derived412 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c412 := by
  apply localUnsat_implies_entails f412 [c118, c410] c412 unsat412 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c410 := derived410 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c413 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f413 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c395, some c13, some c400, some c408, some c409, some c402, some c411, some c412, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p413 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked413 : lratChecker f413 p413 = .success := by decide +kernel
theorem unsat413 : Unsatisfiable (PosFin 31) f413 := by
  apply lratCheckerSound f413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p413
  · intro a ha; simp [p413] at ha; subst a; trivial
  · exact checked413
theorem derived413 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c413 := by
  apply localUnsat_implies_entails f413 [c379, c395, c13, c400, c408, c409, c402, c411, c412] c413 unsat413 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c395 := derived395 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c400 := derived400 a h
  have h4 : Entails.eval a c408 := derived408 a h
  have h5 : Entails.eval a c409 := derived409 a h
  have h6 : Entails.eval a c402 := derived402 a h
  have h7 : Entails.eval a c411 := derived411 a h
  have h8 : Entails.eval a c412 := derived412 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c414 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f414 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c412, some c5, some c126, some c72, some c119, some c95, some c25, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p414 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked414 : lratChecker f414 p414 = .success := by decide +kernel
theorem unsat414 : Unsatisfiable (PosFin 31) f414 := by
  apply lratCheckerSound f414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p414
  · intro a ha; simp [p414] at ha; subst a; trivial
  · exact checked414
theorem derived414 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c414 := by
  apply localUnsat_implies_entails f414 [c379, c412, c5, c126, c72, c119, c95, c25] c414 unsat414 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c412 := derived412 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c415 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f415 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c412, some c5, some c414, some c404, some c12, some c25, some c140, some c1, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p415 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked415 : lratChecker f415 p415 = .success := by decide +kernel
theorem unsat415 : Unsatisfiable (PosFin 31) f415 := by
  apply lratCheckerSound f415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p415
  · intro a ha; simp [p415] at ha; subst a; trivial
  · exact checked415
theorem derived415 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c415 := by
  apply localUnsat_implies_entails f415 [c379, c412, c5, c414, c404, c12, c25, c140, c1] c415 unsat415 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c412 := derived412 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c414 := derived414 a h
  have h4 : Entails.eval a c404 := derived404 a h
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c416 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f416 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c415, some c379, some c5, some c74, some c8, some c140, some c126, some c409, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p416 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked416 : lratChecker f416 p416 = .success := by decide +kernel
theorem unsat416 : Unsatisfiable (PosFin 31) f416 := by
  apply lratCheckerSound f416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p416
  · intro a ha; simp [p416] at ha; subst a; trivial
  · exact checked416
theorem derived416 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c416 := by
  apply localUnsat_implies_entails f416 [c415, c379, c5, c74, c8, c140, c126, c409] c416 unsat416 (by rfl) a
  have h0 : Entails.eval a c415 := derived415 a h
  have h1 : Entails.eval a c379 := derived379 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c140 := h 139 (by decide)
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c409 := derived409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c417 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f417 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c415, some c416, some c79, some c405, some c8, some c90, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p417 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked417 : lratChecker f417 p417 = .success := by decide +kernel
theorem unsat417 : Unsatisfiable (PosFin 31) f417 := by
  apply lratCheckerSound f417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p417
  · intro a ha; simp [p417] at ha; subst a; trivial
  · exact checked417
theorem derived417 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c417 := by
  apply localUnsat_implies_entails f417 [c415, c416, c79, c405, c8, c90] c417 unsat417 (by rfl) a
  have h0 : Entails.eval a c415 := derived415 a h
  have h1 : Entails.eval a c416 := derived416 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c405 := derived405 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c418 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f418 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c413, some c79, some c8, some c59, some c1, some c20, some c30, some c229, some c170, some c232, some c29, some c240, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p418 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked418 : lratChecker f418 p418 = .success := by decide +kernel
theorem unsat418 : Unsatisfiable (PosFin 31) f418 := by
  apply lratCheckerSound f418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p418
  · intro a ha; simp [p418] at ha; subst a; trivial
  · exact checked418
theorem derived418 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c418 := by
  apply localUnsat_implies_entails f418 [c413, c79, c8, c59, c1, c20, c30, c229, c170, c232, c29, c240] c418 unsat418 (by rfl) a
  have h0 : Entails.eval a c413 := derived413 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c232 := h 231 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c419 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f419 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c413, some c418, some c74, some c5, some c417, some c40, some c138, some c229, some c256, some c51, some c60, some c42, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p419 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked419 : lratChecker f419 p419 = .success := by decide +kernel
theorem unsat419 : Unsatisfiable (PosFin 31) f419 := by
  apply lratCheckerSound f419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p419
  · intro a ha; simp [p419] at ha; subst a; trivial
  · exact checked419
theorem derived419 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c419 := by
  apply localUnsat_implies_entails f419 [c379, c413, c418, c74, c5, c417, c40, c138, c229, c256, c51, c60, c42] c419 unsat419 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c413 := derived413 a h
  have h2 : Entails.eval a c418 := derived418 a h
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c417 := derived417 a h
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c256 := h 255 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c420 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f420 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c413, some c418, some c74, some c5, some c417, some c419, some c35, some c339, some c329, some c255, some c60, some c337, some c132, some c94, some c316, some c291, some c169, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p420 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked420 : lratChecker f420 p420 = .success := by decide +kernel
theorem unsat420 : Unsatisfiable (PosFin 31) f420 := by
  apply lratCheckerSound f420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p420
  · intro a ha; simp [p420] at ha; subst a; trivial
  · exact checked420
theorem derived420 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c420 := by
  apply localUnsat_implies_entails f420 [c379, c413, c418, c74, c5, c417, c419, c35, c339, c329, c255, c60, c337, c132, c94, c316, c291, c169] c420 unsat420 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c413 := derived413 a h
  have h2 : Entails.eval a c418 := derived418 a h
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c417 := derived417 a h
  have h6 : Entails.eval a c419 := derived419 a h
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c339 := h 338 (by decide)
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c255 := h 254 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c337 := h 336 (by decide)
  have h13 : Entails.eval a c132 := h 131 (by decide)
  have h14 : Entails.eval a c94 := h 93 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c421 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f421 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c418, some c420, some c95, some c379, some c413, some c74, some c5, some c417, some c42, some c320, some c336, some c51, some c117, some c168, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p421 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked421 : lratChecker f421 p421 = .success := by decide +kernel
theorem unsat421 : Unsatisfiable (PosFin 31) f421 := by
  apply lratCheckerSound f421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p421
  · intro a ha; simp [p421] at ha; subst a; trivial
  · exact checked421
theorem derived421 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c421 := by
  apply localUnsat_implies_entails f421 [c418, c420, c95, c379, c413, c74, c5, c417, c42, c320, c336, c51, c117, c168] c421 unsat421 (by rfl) a
  have h0 : Entails.eval a c418 := derived418 a h
  have h1 : Entails.eval a c420 := derived420 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c413 := derived413 a h
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c417 := derived417 a h
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c320 := h 319 (by decide)
  have h10 : Entails.eval a c336 := h 335 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c422 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f422 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c60, some c288, some c325, some c28, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p422 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked422 : lratChecker f422 p422 = .success := by decide +kernel
theorem unsat422 : Unsatisfiable (PosFin 31) f422 := by
  apply lratCheckerSound f422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p422
  · intro a ha; simp [p422] at ha; subst a; trivial
  · exact checked422
theorem derived422 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c422 := by
  apply localUnsat_implies_entails f422 [c379, c60, c288, c325, c28] c422 unsat422 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c288 := h 287 (by decide)
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c423 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f423 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c418, some c420, some c95, some c379, some c413, some c74, some c320, some c421, some c291, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p423 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked423 : lratChecker f423 p423 = .success := by decide +kernel
theorem unsat423 : Unsatisfiable (PosFin 31) f423 := by
  apply lratCheckerSound f423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p423
  · intro a ha; simp [p423] at ha; subst a; trivial
  · exact checked423
theorem derived423 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c423 := by
  apply localUnsat_implies_entails f423 [c418, c420, c95, c379, c413, c74, c320, c421, c291] c423 unsat423 (by rfl) a
  have h0 : Entails.eval a c418 := derived418 a h
  have h1 : Entails.eval a c420 := derived420 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c413 := derived413 a h
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c421 := derived421 a h
  have h8 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c424 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f424 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c413, some c379, some c418, some c5, some c420, some c70, some c95, some c33, some c423, some c60, some c422, some c256, some c187, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p424 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked424 : lratChecker f424 p424 = .success := by decide +kernel
theorem unsat424 : Unsatisfiable (PosFin 31) f424 := by
  apply lratCheckerSound f424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p424
  · intro a ha; simp [p424] at ha; subst a; trivial
  · exact checked424
theorem derived424 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c424 := by
  apply localUnsat_implies_entails f424 [c413, c379, c418, c5, c420, c70, c95, c33, c423, c60, c422, c256, c187] c424 unsat424 (by rfl) a
  have h0 : Entails.eval a c413 := derived413 a h
  have h1 : Entails.eval a c379 := derived379 a h
  have h2 : Entails.eval a c418 := derived418 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c420 := derived420 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c423 := derived423 a h
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c422 := derived422 a h
  have h11 : Entails.eval a c256 := h 255 (by decide)
  have h12 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c425 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨26, by decide⟩, true), (⟨20, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f425 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c135, some c246, some c31, some c33, some c193, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p425 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked425 : lratChecker f425 p425 = .success := by decide +kernel
theorem unsat425 : Unsatisfiable (PosFin 31) f425 := by
  apply lratCheckerSound f425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p425
  · intro a ha; simp [p425] at ha; subst a; trivial
  · exact checked425
theorem derived425 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c425 := by
  apply localUnsat_implies_entails f425 [c55, c135, c246, c31, c33, c193] c425 unsat425 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c246 := h 245 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c426 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false), (⟨20, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f426 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c60, some c379, some c170, some c187, some c40, some c31, some c172, some c255, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p426 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked426 : lratChecker f426 p426 = .success := by decide +kernel
theorem unsat426 : Unsatisfiable (PosFin 31) f426 := by
  apply lratCheckerSound f426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p426
  · intro a ha; simp [p426] at ha; subst a; trivial
  · exact checked426
theorem derived426 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c426 := by
  apply localUnsat_implies_entails f426 [c60, c379, c170, c187, c40, c31, c172, c255] c426 unsat426 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c379 := derived379 a h
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c187 := h 186 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c427 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨11, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f427 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c413, some c417, some c379, some c60, some c425, some c178, some c116, some c426, some c100, some c74, some c95, some c279, some c138, some c301, some c302, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p427 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked427 : lratChecker f427 p427 = .success := by decide +kernel
theorem unsat427 : Unsatisfiable (PosFin 31) f427 := by
  apply lratCheckerSound f427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p427
  · intro a ha; simp [p427] at ha; subst a; trivial
  · exact checked427
theorem derived427 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c427 := by
  apply localUnsat_implies_entails f427 [c424, c413, c417, c379, c60, c425, c178, c116, c426, c100, c74, c95, c279, c138, c301, c302] c427 unsat427 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c413 := derived413 a h
  have h2 : Entails.eval a c417 := derived417 a h
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c425 := derived425 a h
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c426 := derived426 a h
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c279 := h 278 (by decide)
  have h13 : Entails.eval a c138 := h 137 (by decide)
  have h14 : Entails.eval a c301 := h 300 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c428 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f428 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c413, some c417, some c379, some c325, some c34, some c255, some c50, some c59, some c48, some c233, some c218, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p428 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked428 : lratChecker f428 p428 = .success := by decide +kernel
theorem unsat428 : Unsatisfiable (PosFin 31) f428 := by
  apply lratCheckerSound f428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p428
  · intro a ha; simp [p428] at ha; subst a; trivial
  · exact checked428
theorem derived428 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c428 := by
  apply localUnsat_implies_entails f428 [c424, c413, c417, c379, c325, c34, c255, c50, c59, c48, c233, c218] c428 unsat428 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c413 := derived413 a h
  have h2 : Entails.eval a c417 := derived417 a h
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c233 := h 232 (by decide)
  have h11 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c429 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨26, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c40, some c256, some c187, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p429 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 31) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c40, c256, c187] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c430 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c429, some c325, some c428, some c329, some c297, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p430 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 31) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c379, c429, c325, c428, c329, c297] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c325 := h 324 (by decide)
  have h3 : Entails.eval a c428 := derived428 a h
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c431 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c297, some c41, some c298, some c229, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p431 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 31) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c297, c41, c298, c229] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c297 := h 296 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c298 := h 297 (by decide)
  have h3 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c432 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c295, some c40, some c257, some c155, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p432 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 31) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c379, c295, c40, c257, c155] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨26, by decide⟩, false), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c40, some c138, some c257, some c182, some c51, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p433 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 31) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c379, c40, c138, c257, c182, c51] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨28, by decide⟩, false), (⟨9, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c188, some c183, some c64, some c32, some c319, some c293, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p434 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 31) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c188, c183, c64, c32, c319, c293] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c188 := h 187 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c435 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c413, some c417, some c379, some c427, some c430, some c432, some c431, some c433, some c255, some c188, some c434, some c135, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p435 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 31) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c424, c413, c417, c379, c427, c430, c432, c431, c433, c255, c188, c434, c135] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c413 := derived413 a h
  have h2 : Entails.eval a c417 := derived417 a h
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c427 := derived427 a h
  have h5 : Entails.eval a c430 := derived430 a h
  have h6 : Entails.eval a c432 := derived432 a h
  have h7 : Entails.eval a c431 := derived431 a h
  have h8 : Entails.eval a c433 := derived433 a h
  have h9 : Entails.eval a c255 := h 254 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c434 := derived434 a h
  have h12 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨26, by decide⟩, false), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c295, some c1, some c227, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p436 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 31) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c295, c1, c227] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c295 := h 294 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c435, some c431, some c227, some c328, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p437 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 31) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c435, c431, c227, c328] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c435 := derived435 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c227 := h 226 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c438 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c413, some c379, some c435, some c5, some c79, some c424, some c60, some c186, some c436, some c24, some c437, some c3, some c313, some c195, some c304, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p438 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 31) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c413, c379, c435, c5, c79, c424, c60, c186, c436, c24, c437, c3, c313, c195, c304] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c413 := derived413 a h
  have h1 : Entails.eval a c379 := derived379 a h
  have h2 : Entails.eval a c435 := derived435 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c424 := derived424 a h
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c436 := derived436 a h
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c437 := derived437 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c195 := h 194 (by decide)
  have h14 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c413, some c424, some c435, some c5, some c79, some c438, some c36, some c431, some c3, some c325, some c313, some c256, some c19, some c342, some c272, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p439 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 31) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c379, c413, c424, c435, c5, c79, c438, c36, c431, c3, c325, c313, c256, c19, c342, c272] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c413 := derived413 a h
  have h2 : Entails.eval a c424 := derived424 a h
  have h3 : Entails.eval a c435 := derived435 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c438 := derived438 a h
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c431 := derived431 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c325 := h 324 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c342 := h 341 (by decide)
  have h15 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c440 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨26, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c439, some c379, some c256, some c38, some c187, some c226, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p440 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 31) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c439, c379, c256, c38, c187, c226] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c379 := derived379 a h
  have h2 : Entails.eval a c256 := h 255 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c441 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨26, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c36, some c440, some c325, some c41, some c297, some c260, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p441 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 31) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c379, c36, c440, c325, c41, c297, c260] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c440 := derived440 a h
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c297 := h 296 (by decide)
  have h6 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c439, some c379, some c441, some c429, some c325, some c329, some c297, some c227, some c255, some c187, some c158, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p442 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 31) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c439, c379, c441, c429, c325, c329, c297, c227, c255, c187, c158] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c379 := derived379 a h
  have h2 : Entails.eval a c441 := derived441 a h
  have h3 : Entails.eval a c429 := derived429 a h
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived442

end CochromaticTwenty.Certificates.Z12Direct_5_7_13
