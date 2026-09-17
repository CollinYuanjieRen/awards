import MerLeanExperiment.Certificates.Z12Direct_5_7_13.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_7_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c443 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c439, some c442, some c326, some c432, some c379, some c67, some c255, some c297, some c1, some c41, some c4, some c185, some c417, some c79, some c60, some c124, some c182, some c199, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p443 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 31) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c439, c442, c326, c432, c379, c67, c255, c297, c1, c41, c4, c185, c417, c79, c60, c124, c182, c199] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c442 := derived442 a h
  have h2 : Entails.eval a c326 := h 325 (by decide)
  have h3 : Entails.eval a c432 := derived432 a h
  have h4 : Entails.eval a c379 := derived379 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c417 := derived417 a h
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c60 := h 59 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c182 := h 181 (by decide)
  have h17 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c444 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f444 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c439, some c442, some c326, some c432, some c379, some c67, some c255, some c297, some c1, some c41, some c4, some c185, some c202, some c282, some c199, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p444 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked444 : lratChecker f444 p444 = .success := by decide +kernel
theorem unsat444 : Unsatisfiable (PosFin 31) f444 := by
  apply lratCheckerSound f444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p444
  · intro a ha; simp [p444] at ha; subst a; trivial
  · exact checked444
theorem derived444 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c444 := by
  apply localUnsat_implies_entails f444 [c439, c442, c326, c432, c379, c67, c255, c297, c1, c41, c4, c185, c202, c282, c199] c444 unsat444 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c442 := derived442 a h
  have h2 : Entails.eval a c326 := h 325 (by decide)
  have h3 : Entails.eval a c432 := derived432 a h
  have h4 : Entails.eval a c379 := derived379 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c282 := h 281 (by decide)
  have h14 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c445 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f445 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c443, some c439, some c442, some c326, some c432, some c379, some c67, some c255, some c297, some c1, some c104, some c22, some c13, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p445 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked445 : lratChecker f445 p445 = .success := by decide +kernel
theorem unsat445 : Unsatisfiable (PosFin 31) f445 := by
  apply lratCheckerSound f445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p445
  · intro a ha; simp [p445] at ha; subst a; trivial
  · exact checked445
theorem derived445 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c445 := by
  apply localUnsat_implies_entails f445 [c443, c439, c442, c326, c432, c379, c67, c255, c297, c1, c104, c22, c13] c445 unsat445 (by rfl) a
  have h0 : Entails.eval a c443 := derived443 a h
  have h1 : Entails.eval a c439 := derived439 a h
  have h2 : Entails.eval a c442 := derived442 a h
  have h3 : Entails.eval a c326 := h 325 (by decide)
  have h4 : Entails.eval a c432 := derived432 a h
  have h5 : Entails.eval a c379 := derived379 a h
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c255 := h 254 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c446 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f446 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c439, some c442, some c67, some c379, some c326, some c432, some c255, some c41, some c297, some c185, some c4, some c1, some c445, some c444, some c192, some c280, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p446 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked446 : lratChecker f446 p446 = .success := by decide +kernel
theorem unsat446 : Unsatisfiable (PosFin 31) f446 := by
  apply lratCheckerSound f446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p446
  · intro a ha; simp [p446] at ha; subst a; trivial
  · exact checked446
theorem derived446 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c446 := by
  apply localUnsat_implies_entails f446 [c439, c442, c67, c379, c326, c432, c255, c41, c297, c185, c4, c1, c445, c444, c192, c280] c446 unsat446 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c442 := derived442 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c432 := derived432 a h
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c445 := derived445 a h
  have h13 : Entails.eval a c444 := derived444 a h
  have h14 : Entails.eval a c192 := h 191 (by decide)
  have h15 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c447 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f447 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c79, some c104, some c22, some c13, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p447 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked447 : lratChecker f447 p447 = .success := by decide +kernel
theorem unsat447 : Unsatisfiable (PosFin 31) f447 := by
  apply lratCheckerSound f447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p447
  · intro a ha; simp [p447] at ha; subst a; trivial
  · exact checked447
theorem derived447 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c447 := by
  apply localUnsat_implies_entails f447 [c79, c104, c22, c13] c447 unsat447 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c448 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f448 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c442, some c446, some c186, some c379, some c439, some c67, some c5, some c447, some c436, some c296, some c155, some c227, some c239, some c97, some c51, some c235, some c176, some c248, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p448 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked448 : lratChecker f448 p448 = .success := by decide +kernel
theorem unsat448 : Unsatisfiable (PosFin 31) f448 := by
  apply lratCheckerSound f448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p448
  · intro a ha; simp [p448] at ha; subst a; trivial
  · exact checked448
theorem derived448 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c448 := by
  apply localUnsat_implies_entails f448 [c442, c446, c186, c379, c439, c67, c5, c447, c436, c296, c155, c227, c239, c97, c51, c235, c176, c248] c448 unsat448 (by rfl) a
  have h0 : Entails.eval a c442 := derived442 a h
  have h1 : Entails.eval a c446 := derived446 a h
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c439 := derived439 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c447 := derived447 a h
  have h8 : Entails.eval a c436 := derived436 a h
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c227 := h 226 (by decide)
  have h12 : Entails.eval a c239 := h 238 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c235 := h 234 (by decide)
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c449 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f449 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c379, some c439, some c442, some c67, some c446, some c5, some c186, some c447, some c436, some c296, some c155, some c227, some c448, some c417, some c60, some c232, some c72, some c182, some c24, some c179, some c51, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p449 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked449 : lratChecker f449 p449 = .success := by decide +kernel
theorem unsat449 : Unsatisfiable (PosFin 31) f449 := by
  apply lratCheckerSound f449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p449
  · intro a ha; simp [p449] at ha; subst a; trivial
  · exact checked449
theorem derived449 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c449 := by
  apply localUnsat_implies_entails f449 [c379, c439, c442, c67, c446, c5, c186, c447, c436, c296, c155, c227, c448, c417, c60, c232, c72, c182, c24, c179, c51] c449 unsat449 (by rfl) a
  have h0 : Entails.eval a c379 := derived379 a h
  have h1 : Entails.eval a c439 := derived439 a h
  have h2 : Entails.eval a c442 := derived442 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c446 := derived446 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c186 := h 185 (by decide)
  have h7 : Entails.eval a c447 := derived447 a h
  have h8 : Entails.eval a c436 := derived436 a h
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c227 := h 226 (by decide)
  have h12 : Entails.eval a c448 := derived448 a h
  have h13 : Entails.eval a c417 := derived417 a h
  have h14 : Entails.eval a c60 := h 59 (by decide)
  have h15 : Entails.eval a c232 := h 231 (by decide)
  have h16 : Entails.eval a c72 := h 71 (by decide)
  have h17 : Entails.eval a c182 := h 181 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c179 := h 178 (by decide)
  have h20 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c450 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f450 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c225, some c326, some c67, some c184, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p450 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked450 : lratChecker f450 p450 = .success := by decide +kernel
theorem unsat450 : Unsatisfiable (PosFin 31) f450 := by
  apply lratCheckerSound f450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p450
  · intro a ha; simp [p450] at ha; subst a; trivial
  · exact checked450
theorem derived450 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c450 := by
  apply localUnsat_implies_entails f450 [c449, c225, c326, c67, c184] c450 unsat450 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c225 := h 224 (by decide)
  have h2 : Entails.eval a c326 := h 325 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c451 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f451 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c450, some c294, some c324, some c255, some c67, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p451 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked451 : lratChecker f451 p451 = .success := by decide +kernel
theorem unsat451 : Unsatisfiable (PosFin 31) f451 := by
  apply lratCheckerSound f451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p451
  · intro a ha; simp [p451] at ha; subst a; trivial
  · exact checked451
theorem derived451 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c451 := by
  apply localUnsat_implies_entails f451 [c449, c450, c294, c324, c255, c67] c451 unsat451 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c450 := derived450 a h
  have h2 : Entails.eval a c294 := h 293 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c452 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨10, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f452 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c67, some c225, some c119, some c134, some c250, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p452 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked452 : lratChecker f452 p452 = .success := by decide +kernel
theorem unsat452 : Unsatisfiable (PosFin 31) f452 := by
  apply lratCheckerSound f452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p452
  · intro a ha; simp [p452] at ha; subst a; trivial
  · exact checked452
theorem derived452 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c452 := by
  apply localUnsat_implies_entails f452 [c449, c67, c225, c119, c134, c250] c452 unsat452 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c453 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f453 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c451, some c41, some c452, some c224, some c225, some c296, some c155, some c258, some c72, some c97, some c278, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p453 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked453 : lratChecker f453 p453 = .success := by decide +kernel
theorem unsat453 : Unsatisfiable (PosFin 31) f453 := by
  apply lratCheckerSound f453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p453
  · intro a ha; simp [p453] at ha; subst a; trivial
  · exact checked453
theorem derived453 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c453 := by
  apply localUnsat_implies_entails f453 [c449, c451, c41, c452, c224, c225, c296, c155, c258, c72, c97, c278] c453 unsat453 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c451 := derived451 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c452 := derived452 a h
  have h4 : Entails.eval a c224 := h 223 (by decide)
  have h5 : Entails.eval a c225 := h 224 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c155 := h 154 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c454 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f454 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c296, some c40, some c156, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p454 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked454 : lratChecker f454 p454 = .success := by decide +kernel
theorem unsat454 : Unsatisfiable (PosFin 31) f454 := by
  apply lratCheckerSound f454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p454
  · intro a ha; simp [p454] at ha; subst a; trivial
  · exact checked454
theorem derived454 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c454 := by
  apply localUnsat_implies_entails f454 [c449, c296, c40, c156] c454 unsat454 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c455 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f455 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c453, some c39, some c454, some c224, some c119, some c134, some c154, some c322, some c156, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p455 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked455 : lratChecker f455 p455 = .success := by decide +kernel
theorem unsat455 : Unsatisfiable (PosFin 31) f455 := by
  apply lratCheckerSound f455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p455
  · intro a ha; simp [p455] at ha; subst a; trivial
  · exact checked455
theorem derived455 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c455 := by
  apply localUnsat_implies_entails f455 [c449, c453, c39, c454, c224, c119, c134, c154, c322, c156] c455 unsat455 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c454 := derived454 a h
  have h4 : Entails.eval a c224 := h 223 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c322 := h 321 (by decide)
  have h9 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c456 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f456 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c453, some c455, some c67, some c156, some c257, some c119, some c134, some c250, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p456 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked456 : lratChecker f456 p456 = .success := by decide +kernel
theorem unsat456 : Unsatisfiable (PosFin 31) f456 := by
  apply lratCheckerSound f456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p456
  · intro a ha; simp [p456] at ha; subst a; trivial
  · exact checked456
theorem derived456 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c456 := by
  apply localUnsat_implies_entails f456 [c449, c453, c455, c67, c156, c257, c119, c134, c250] c456 unsat456 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c455 := derived455 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c257 := h 256 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c457 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f457 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c201, some c207, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p457 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked457 : lratChecker f457 p457 = .success := by decide +kernel
theorem unsat457 : Unsatisfiable (PosFin 31) f457 := by
  apply lratCheckerSound f457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p457
  · intro a ha; simp [p457] at ha; subst a; trivial
  · exact checked457
theorem derived457 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c457 := by
  apply localUnsat_implies_entails f457 [c449, c201, c207] c457 unsat457 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c458 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f458 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c134, some c119, some c456, some c294, some c150, some c457, some c31, some c27, some c292, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p458 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked458 : lratChecker f458 p458 = .success := by decide +kernel
theorem unsat458 : Unsatisfiable (PosFin 31) f458 := by
  apply lratCheckerSound f458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p458
  · intro a ha; simp [p458] at ha; subst a; trivial
  · exact checked458
theorem derived458 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c458 := by
  apply localUnsat_implies_entails f458 [c449, c134, c119, c456, c294, c150, c457, c31, c27, c292] c458 unsat458 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c456 := derived456 a h
  have h4 : Entails.eval a c294 := h 293 (by decide)
  have h5 : Entails.eval a c150 := h 149 (by decide)
  have h6 : Entails.eval a c457 := derived457 a h
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c459 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨23, by decide⟩, true), (⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f459 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c230, some c234, some c48, some c57, some c46, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p459 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked459 : lratChecker f459 p459 = .success := by decide +kernel
theorem unsat459 : Unsatisfiable (PosFin 31) f459 := by
  apply lratCheckerSound f459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p459
  · intro a ha; simp [p459] at ha; subst a; trivial
  · exact checked459
theorem derived459 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c459 := by
  apply localUnsat_implies_entails f459 [c230, c234, c48, c57, c46] c459 unsat459 (by rfl) a
  have h0 : Entails.eval a c230 := h 229 (by decide)
  have h1 : Entails.eval a c234 := h 233 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c460 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f460 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c456, some c119, some c1, some c134, some c458, some c459, some c157, some c187, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p460 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked460 : lratChecker f460 p460 = .success := by decide +kernel
theorem unsat460 : Unsatisfiable (PosFin 31) f460 := by
  apply lratCheckerSound f460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p460
  · intro a ha; simp [p460] at ha; subst a; trivial
  · exact checked460
theorem derived460 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c460 := by
  apply localUnsat_implies_entails f460 [c456, c119, c1, c134, c458, c459, c157, c187] c460 unsat460 (by rfl) a
  have h0 : Entails.eval a c456 := derived456 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c458 := derived458 a h
  have h5 : Entails.eval a c459 := derived459 a h
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c461 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f461 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c157, some c187, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p461 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked461 : lratChecker f461 p461 = .success := by decide +kernel
theorem unsat461 : Unsatisfiable (PosFin 31) f461 := by
  apply lratCheckerSound f461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p461
  · intro a ha; simp [p461] at ha; subst a; trivial
  · exact checked461
theorem derived461 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c461 := by
  apply localUnsat_implies_entails f461 [c226, c157, c187] c461 unsat461 (by rfl) a
  have h0 : Entails.eval a c226 := h 225 (by decide)
  have h1 : Entails.eval a c157 := h 156 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c462 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f462 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c207, some c150, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p462 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked462 : lratChecker f462 p462 = .success := by decide +kernel
theorem unsat462 : Unsatisfiable (PosFin 31) f462 := by
  apply lratCheckerSound f462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p462
  · intro a ha; simp [p462] at ha; subst a; trivial
  · exact checked462
theorem derived462 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c462 := by
  apply localUnsat_implies_entails f462 [c449, c207, c150] c462 unsat462 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c463 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, false), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f463 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c2, some c6, some c156, some c462, some c64, some c213, some c269, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p463 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked463 : lratChecker f463 p463 = .success := by decide +kernel
theorem unsat463 : Unsatisfiable (PosFin 31) f463 := by
  apply lratCheckerSound f463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p463
  · intro a ha; simp [p463] at ha; subst a; trivial
  · exact checked463
theorem derived463 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c463 := by
  apply localUnsat_implies_entails f463 [c449, c2, c6, c156, c462, c64, c213, c269] c463 unsat463 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c462 := derived462 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c464 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f464 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c456, some c460, some c461, some c156, some c429, some c40, some c37, some c229, some c327, some c2, some c463, some c55, some c28, some c108, some c14, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p464 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked464 : lratChecker f464 p464 = .success := by decide +kernel
theorem unsat464 : Unsatisfiable (PosFin 31) f464 := by
  apply lratCheckerSound f464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p464
  · intro a ha; simp [p464] at ha; subst a; trivial
  · exact checked464
theorem derived464 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c464 := by
  apply localUnsat_implies_entails f464 [c449, c456, c460, c461, c156, c429, c40, c37, c229, c327, c2, c463, c55, c28, c108, c14] c464 unsat464 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c456 := derived456 a h
  have h2 : Entails.eval a c460 := derived460 a h
  have h3 : Entails.eval a c461 := derived461 a h
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c429 := derived429 a h
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c327 := h 326 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c463 := derived463 a h
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c465 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f465 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c26, some c30, some c8, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p465 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked465 : lratChecker f465 p465 = .success := by decide +kernel
theorem unsat465 : Unsatisfiable (PosFin 31) f465 := by
  apply lratCheckerSound f465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p465
  · intro a ha; simp [p465] at ha; subst a; trivial
  · exact checked465
theorem derived465 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c465 := by
  apply localUnsat_implies_entails f465 [c26, c30, c8] c465 unsat465 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c466 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f466 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c464, some c39, some c465, some c224, some c1, some c154, some c184, some c38, some c327, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p466 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked466 : lratChecker f466 p466 = .success := by decide +kernel
theorem unsat466 : Unsatisfiable (PosFin 31) f466 := by
  apply lratCheckerSound f466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p466
  · intro a ha; simp [p466] at ha; subst a; trivial
  · exact checked466
theorem derived466 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c466 := by
  apply localUnsat_implies_entails f466 [c449, c464, c39, c465, c224, c1, c154, c184, c38, c327] c466 unsat466 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c464 := derived464 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c465 := derived465 a h
  have h4 : Entails.eval a c224 := h 223 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c467 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f467 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c224, some c41, some c154, some c184, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p467 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked467 : lratChecker f467 p467 = .success := by decide +kernel
theorem unsat467 : Unsatisfiable (PosFin 31) f467 := by
  apply lratCheckerSound f467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p467
  · intro a ha; simp [p467] at ha; subst a; trivial
  · exact checked467
theorem derived467 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c467 := by
  apply localUnsat_implies_entails f467 [c449, c224, c41, c154, c184] c467 unsat467 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c224 := h 223 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c468 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f468 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c258, some c325, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p468 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked468 : lratChecker f468 p468 = .success := by decide +kernel
theorem unsat468 : Unsatisfiable (PosFin 31) f468 := by
  apply lratCheckerSound f468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p468
  · intro a ha; simp [p468] at ha; subst a; trivial
  · exact checked468
theorem derived468 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c468 := by
  apply localUnsat_implies_entails f468 [c41, c258, c325] c468 unsat468 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c469 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f469 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c466, some c456, some c119, some c1, some c134, some c12, some c467, some c468, some c2, some c294, some c340, some c459, some c141, some c127, some c174, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p469 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked469 : lratChecker f469 p469 = .success := by decide +kernel
theorem unsat469 : Unsatisfiable (PosFin 31) f469 := by
  apply lratCheckerSound f469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p469
  · intro a ha; simp [p469] at ha; subst a; trivial
  · exact checked469
theorem derived469 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c469 := by
  apply localUnsat_implies_entails f469 [c449, c466, c456, c119, c1, c134, c12, c467, c468, c2, c294, c340, c459, c141, c127, c174] c469 unsat469 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c466 := derived466 a h
  have h2 : Entails.eval a c456 := derived456 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c467 := derived467 a h
  have h8 : Entails.eval a c468 := derived468 a h
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c340 := h 339 (by decide)
  have h12 : Entails.eval a c459 := derived459 a h
  have h13 : Entails.eval a c141 := h 140 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c470 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, true), (⟨28, by decide⟩, false), (⟨25, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f470 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c141, some c23, some c84, some c189, some c178, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p470 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked470 : lratChecker f470 p470 = .success := by decide +kernel
theorem unsat470 : Unsatisfiable (PosFin 31) f470 := by
  apply lratCheckerSound f470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p470
  · intro a ha; simp [p470] at ha; subst a; trivial
  · exact checked470
theorem derived470 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c470 := by
  apply localUnsat_implies_entails f470 [c449, c141, c23, c84, c189, c178] c470 unsat470 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c471 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨2, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f471 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c225, some c55, some c53, some c142, some c14, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p471 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked471 : lratChecker f471 p471 = .success := by decide +kernel
theorem unsat471 : Unsatisfiable (PosFin 31) f471 := by
  apply lratCheckerSound f471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p471
  · intro a ha; simp [p471] at ha; subst a; trivial
  · exact checked471
theorem derived471 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c471 := by
  apply localUnsat_implies_entails f471 [c449, c225, c55, c53, c142, c14] c471 unsat471 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c225 := h 224 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c472 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f472 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c141, some c23, some c128, some c189, some c178, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p472 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked472 : lratChecker f472 p472 = .success := by decide +kernel
theorem unsat472 : Unsatisfiable (PosFin 31) f472 := by
  apply lratCheckerSound f472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p472
  · intro a ha; simp [p472] at ha; subst a; trivial
  · exact checked472
theorem derived472 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c472 := by
  apply localUnsat_implies_entails f472 [c449, c141, c23, c128, c189, c178] c472 unsat472 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c473 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f473 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c469, some c465, some c6, some c466, some c456, some c256, some c2, some c471, some c472, some c340, some c64, some c210, some c269, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p473 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked473 : lratChecker f473 p473 = .success := by decide +kernel
theorem unsat473 : Unsatisfiable (PosFin 31) f473 := by
  apply lratCheckerSound f473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p473
  · intro a ha; simp [p473] at ha; subst a; trivial
  · exact checked473
theorem derived473 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c473 := by
  apply localUnsat_implies_entails f473 [c449, c469, c465, c6, c466, c456, c256, c2, c471, c472, c340, c64, c210, c269] c473 unsat473 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c469 := derived469 a h
  have h2 : Entails.eval a c465 := derived465 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c466 := derived466 a h
  have h5 : Entails.eval a c456 := derived456 a h
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c471 := derived471 a h
  have h9 : Entails.eval a c472 := derived472 a h
  have h10 : Entails.eval a c340 := h 339 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c474 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f474 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c456, some c466, some c469, some c256, some c465, some c473, some c41, some c258, some c299, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p474 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked474 : lratChecker f474 p474 = .success := by decide +kernel
theorem unsat474 : Unsatisfiable (PosFin 31) f474 := by
  apply lratCheckerSound f474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p474
  · intro a ha; simp [p474] at ha; subst a; trivial
  · exact checked474
theorem derived474 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c474 := by
  apply localUnsat_implies_entails f474 [c456, c466, c469, c256, c465, c473, c41, c258, c299] c474 unsat474 (by rfl) a
  have h0 : Entails.eval a c456 := derived456 a h
  have h1 : Entails.eval a c466 := derived466 a h
  have h2 : Entails.eval a c469 := derived469 a h
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c465 := derived465 a h
  have h5 : Entails.eval a c473 := derived473 a h
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c475 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f475 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c474, some c258, some c1, some c72, some c225, some c278, some c53, some c238, some c146, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p475 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked475 : lratChecker f475 p475 = .success := by decide +kernel
theorem unsat475 : Unsatisfiable (PosFin 31) f475 := by
  apply lratCheckerSound f475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p475
  · intro a ha; simp [p475] at ha; subst a; trivial
  · exact checked475
theorem derived475 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c475 := by
  apply localUnsat_implies_entails f475 [c449, c474, c258, c1, c72, c225, c278, c53, c238, c146] c475 unsat475 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c474 := derived474 a h
  have h2 : Entails.eval a c258 := h 257 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c225 := h 224 (by decide)
  have h6 : Entails.eval a c278 := h 277 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c238 := h 237 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c476 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f476 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c157, some c53, some c30, some c31, some c291, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p476 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked476 : lratChecker f476 p476 = .success := by decide +kernel
theorem unsat476 : Unsatisfiable (PosFin 31) f476 := by
  apply lratCheckerSound f476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p476
  · intro a ha; simp [p476] at ha; subst a; trivial
  · exact checked476
theorem derived476 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c476 := by
  apply localUnsat_implies_entails f476 [c157, c53, c30, c31, c291] c476 unsat476 (by rfl) a
  have h0 : Entails.eval a c157 := h 156 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c477 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f477 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c298, some c229, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p477 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked477 : lratChecker f477 p477 = .success := by decide +kernel
theorem unsat477 : Unsatisfiable (PosFin 31) f477 := by
  apply lratCheckerSound f477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p477
  · intro a ha; simp [p477] at ha; subst a; trivial
  · exact checked477
theorem derived477 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c477 := by
  apply localUnsat_implies_entails f477 [c298, c229] c477 unsat477 (by rfl) a
  have h0 : Entails.eval a c298 := h 297 (by decide)
  have h1 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c478 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f478 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c477, some c157, some c454, some c40, some c260, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p478 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked478 : lratChecker f478 p478 = .success := by decide +kernel
theorem unsat478 : Unsatisfiable (PosFin 31) f478 := by
  apply lratCheckerSound f478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p478
  · intro a ha; simp [p478] at ha; subst a; trivial
  · exact checked478
theorem derived478 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c478 := by
  apply localUnsat_implies_entails f478 [c477, c157, c454, c40, c260] c478 unsat478 (by rfl) a
  have h0 : Entails.eval a c477 := derived477 a h
  have h1 : Entails.eval a c157 := h 156 (by decide)
  have h2 : Entails.eval a c454 := derived454 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c479 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f479 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c475, some c474, some c157, some c476, some c30, some c226, some c332, some c270, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p479 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked479 : lratChecker f479 p479 = .success := by decide +kernel
theorem unsat479 : Unsatisfiable (PosFin 31) f479 := by
  apply lratCheckerSound f479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p479
  · intro a ha; simp [p479] at ha; subst a; trivial
  · exact checked479
theorem derived479 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c479 := by
  apply localUnsat_implies_entails f479 [c475, c474, c157, c476, c30, c226, c332, c270] c479 unsat479 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c474 := derived474 a h
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c476 := derived476 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c480 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f480 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c475, some c478, some c327, some c479, some c156, some c37, some c40, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p480 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked480 : lratChecker f480 p480 = .success := by decide +kernel
theorem unsat480 : Unsatisfiable (PosFin 31) f480 := by
  apply lratCheckerSound f480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p480
  · intro a ha; simp [p480] at ha; subst a; trivial
  · exact checked480
theorem derived480 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c480 := by
  apply localUnsat_implies_entails f480 [c449, c475, c478, c327, c479, c156, c37, c40] c480 unsat480 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c475 := derived475 a h
  have h2 : Entails.eval a c478 := derived478 a h
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c479 := derived479 a h
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c481 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f481 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c474, some c480, some c119, some c1, some c327, some c224, some c228, some c31, some c251, some c179, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p481 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked481 : lratChecker f481 p481 = .success := by decide +kernel
theorem unsat481 : Unsatisfiable (PosFin 31) f481 := by
  apply lratCheckerSound f481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p481
  · intro a ha; simp [p481] at ha; subst a; trivial
  · exact checked481
theorem derived481 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c481 := by
  apply localUnsat_implies_entails f481 [c449, c474, c480, c119, c1, c327, c224, c228, c31, c251, c179] c481 unsat481 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c474 := derived474 a h
  have h2 : Entails.eval a c480 := derived480 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c327 := h 326 (by decide)
  have h6 : Entails.eval a c224 := h 223 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c251 := h 250 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c482 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f482 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c119, some c481, some c474, some c31, some c185, some c251, some c179, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p482 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked482 : lratChecker f482 p482 = .success := by decide +kernel
theorem unsat482 : Unsatisfiable (PosFin 31) f482 := by
  apply lratCheckerSound f482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p482
  · intro a ha; simp [p482] at ha; subst a; trivial
  · exact checked482
theorem derived482 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c482 := by
  apply localUnsat_implies_entails f482 [c119, c481, c474, c31, c185, c251, c179] c482 unsat482 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c481 := derived481 a h
  have h2 : Entails.eval a c474 := derived474 a h
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c185 := h 184 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c483 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f483 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c1, some c228, some c41, some c187, some c67, some c250, some c156, some c28, some c222, some c146, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p483 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked483 : lratChecker f483 p483 = .success := by decide +kernel
theorem unsat483 : Unsatisfiable (PosFin 31) f483 := by
  apply lratCheckerSound f483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p483
  · intro a ha; simp [p483] at ha; subst a; trivial
  · exact checked483
theorem derived483 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c483 := by
  apply localUnsat_implies_entails f483 [c449, c1, c228, c41, c187, c67, c250, c156, c28, c222, c146] c483 unsat483 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c250 := h 249 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c222 := h 221 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c484 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨23, by decide⟩, true), (⟨1, by decide⟩, true), (⟨7, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f484 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c483, some c39, some c467, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p484 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked484 : lratChecker f484 p484 = .success := by decide +kernel
theorem unsat484 : Unsatisfiable (PosFin 31) f484 := by
  apply lratCheckerSound f484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p484
  · intro a ha; simp [p484] at ha; subst a; trivial
  · exact checked484
theorem derived484 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c484 := by
  apply localUnsat_implies_entails f484 [c449, c483, c39, c467] c484 unsat484 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c483 := derived483 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c467 := derived467 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c485 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f485 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c481, some c474, some c119, some c482, some c484, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p485 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked485 : lratChecker f485 p485 = .success := by decide +kernel
theorem unsat485 : Unsatisfiable (PosFin 31) f485 := by
  apply lratCheckerSound f485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p485
  · intro a ha; simp [p485] at ha; subst a; trivial
  · exact checked485
theorem derived485 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c485 := by
  apply localUnsat_implies_entails f485 [c481, c474, c119, c482, c484] c485 unsat485 (by rfl) a
  have h0 : Entails.eval a c481 := derived481 a h
  have h1 : Entails.eval a c474 := derived474 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c482 := derived482 a h
  have h4 : Entails.eval a c484 := derived484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c486 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f486 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c39, some c155, some c41, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p486 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked486 : lratChecker f486 p486 = .success := by decide +kernel
theorem unsat486 : Unsatisfiable (PosFin 31) f486 := by
  apply lratCheckerSound f486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p486
  · intro a ha; simp [p486] at ha; subst a; trivial
  · exact checked486
theorem derived486 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c486 := by
  apply localUnsat_implies_entails f486 [c449, c39, c155, c41] c486 unsat486 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c487 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨28, by decide⟩, false), (⟨7, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f487 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c256, some c225, some c67, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p487 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked487 : lratChecker f487 p487 = .success := by decide +kernel
theorem unsat487 : Unsatisfiable (PosFin 31) f487 := by
  apply lratCheckerSound f487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p487
  · intro a ha; simp [p487] at ha; subst a; trivial
  · exact checked487
theorem derived487 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c487 := by
  apply localUnsat_implies_entails f487 [c449, c256, c225, c67] c487 unsat487 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c488 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨29, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f488 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c486, some c487, some c187, some c257, some c67, some c156, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p488 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked488 : lratChecker f488 p488 = .success := by decide +kernel
theorem unsat488 : Unsatisfiable (PosFin 31) f488 := by
  apply lratCheckerSound f488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p488
  · intro a ha; simp [p488] at ha; subst a; trivial
  · exact checked488
theorem derived488 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c488 := by
  apply localUnsat_implies_entails f488 [c449, c486, c487, c187, c257, c67, c156] c488 unsat488 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c486 := derived486 a h
  have h2 : Entails.eval a c487 := derived487 a h
  have h3 : Entails.eval a c187 := h 186 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c489 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f489 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c488, some c40, some c185, some c487, some c226, some c156, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p489 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked489 : lratChecker f489 p489 = .success := by decide +kernel
theorem unsat489 : Unsatisfiable (PosFin 31) f489 := by
  apply lratCheckerSound f489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p489
  · intro a ha; simp [p489] at ha; subst a; trivial
  · exact checked489
theorem derived489 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c489 := by
  apply localUnsat_implies_entails f489 [c449, c488, c40, c185, c487, c226, c156] c489 unsat489 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c488 := derived488 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c185 := h 184 (by decide)
  have h4 : Entails.eval a c487 := derived487 a h
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c490 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f490 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c481, some c485, some c489, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p490 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked490 : lratChecker f490 p490 = .success := by decide +kernel
theorem unsat490 : Unsatisfiable (PosFin 31) f490 := by
  apply lratCheckerSound f490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p490
  · intro a ha; simp [p490] at ha; subst a; trivial
  · exact checked490
theorem derived490 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c490 := by
  apply localUnsat_implies_entails f490 [c481, c485, c489] c490 unsat490 (by rfl) a
  have h0 : Entails.eval a c481 := derived481 a h
  have h1 : Entails.eval a c485 := derived485 a h
  have h2 : Entails.eval a c489 := derived489 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c491 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, false), (⟨29, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f491 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c40, some c184, some c36, some c487, some c454, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p491 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked491 : lratChecker f491 p491 = .success := by decide +kernel
theorem unsat491 : Unsatisfiable (PosFin 31) f491 := by
  apply lratCheckerSound f491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p491
  · intro a ha; simp [p491] at ha; subst a; trivial
  · exact checked491
theorem derived491 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c491 := by
  apply localUnsat_implies_entails f491 [c449, c40, c184, c36, c487, c454] c491 unsat491 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c487 := derived487 a h
  have h5 : Entails.eval a c454 := derived454 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c492 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f492 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c487, some c187, some c257, some c67, some c156, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p492 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked492 : lratChecker f492 p492 = .success := by decide +kernel
theorem unsat492 : Unsatisfiable (PosFin 31) f492 := by
  apply lratCheckerSound f492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p492
  · intro a ha; simp [p492] at ha; subst a; trivial
  · exact checked492
theorem derived492 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c492 := by
  apply localUnsat_implies_entails f492 [c449, c487, c187, c257, c67, c156] c492 unsat492 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c487 := derived487 a h
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c493 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨29, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f493 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c491, some c492, some c39, some c451, some c256, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p493 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked493 : lratChecker f493 p493 = .success := by decide +kernel
theorem unsat493 : Unsatisfiable (PosFin 31) f493 := by
  apply lratCheckerSound f493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p493
  · intro a ha; simp [p493] at ha; subst a; trivial
  · exact checked493
theorem derived493 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c493 := by
  apply localUnsat_implies_entails f493 [c449, c491, c492, c39, c451, c256] c493 unsat493 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c492 := derived492 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c494 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f494 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c490, some c493, some c294, some c255, some c1, some c259, some c158, some c67, some c187, some c7, some c119, some c470, some c340, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p494 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked494 : lratChecker f494 p494 = .success := by decide +kernel
theorem unsat494 : Unsatisfiable (PosFin 31) f494 := by
  apply lratCheckerSound f494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p494
  · intro a ha; simp [p494] at ha; subst a; trivial
  · exact checked494
theorem derived494 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c494 := by
  apply localUnsat_implies_entails f494 [c449, c490, c493, c294, c255, c1, c259, c158, c67, c187, c7, c119, c470, c340] c494 unsat494 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c490 := derived490 a h
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c259 := h 258 (by decide)
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c470 := derived470 a h
  have h13 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c495 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f495 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c490, some c474, some c493, some c119, some c1, some c294, some c7, some c255, some c259, some c67, some c158, some c325, some c6, some c494, some c28, some c211, some c146, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p495 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked495 : lratChecker f495 p495 = .success := by decide +kernel
theorem unsat495 : Unsatisfiable (PosFin 31) f495 := by
  apply lratCheckerSound f495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p495
  · intro a ha; simp [p495] at ha; subst a; trivial
  · exact checked495
theorem derived495 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c495 := by
  apply localUnsat_implies_entails f495 [c449, c490, c474, c493, c119, c1, c294, c7, c255, c259, c67, c158, c325, c6, c494, c28, c211, c146] c495 unsat495 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c490 := derived490 a h
  have h2 : Entails.eval a c474 := derived474 a h
  have h3 : Entails.eval a c493 := derived493 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c325 := h 324 (by decide)
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c494 := derived494 a h
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c496 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f496 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c490, some c259, some c2, some c495, some c49, some c211, some c261, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p496 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked496 : lratChecker f496 p496 = .success := by decide +kernel
theorem unsat496 : Unsatisfiable (PosFin 31) f496 := by
  apply lratCheckerSound f496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p496
  · intro a ha; simp [p496] at ha; subst a; trivial
  · exact checked496
theorem derived496 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c496 := by
  apply localUnsat_implies_entails f496 [c490, c259, c2, c495, c49, c211, c261] c496 unsat496 (by rfl) a
  have h0 : Entails.eval a c490 := derived490 a h
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c495 := derived495 a h
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c211 := h 210 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c497 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f497 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c490, some c2, some c495, some c474, some c496, some c340, some c107, some c106, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p497 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked497 : lratChecker f497 p497 = .success := by decide +kernel
theorem unsat497 : Unsatisfiable (PosFin 31) f497 := by
  apply lratCheckerSound f497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p497
  · intro a ha; simp [p497] at ha; subst a; trivial
  · exact checked497
theorem derived497 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c497 := by
  apply localUnsat_implies_entails f497 [c490, c2, c495, c474, c496, c340, c107, c106] c497 unsat497 (by rfl) a
  have h0 : Entails.eval a c490 := derived490 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c495 := derived495 a h
  have h3 : Entails.eval a c474 := derived474 a h
  have h4 : Entails.eval a c496 := derived496 a h
  have h5 : Entails.eval a c340 := h 339 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c498 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f498 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c490, some c2, some c340, some c472, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p498 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked498 : lratChecker f498 p498 = .success := by decide +kernel
theorem unsat498 : Unsatisfiable (PosFin 31) f498 := by
  apply lratCheckerSound f498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p498
  · intro a ha; simp [p498] at ha; subst a; trivial
  · exact checked498
theorem derived498 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c498 := by
  apply localUnsat_implies_entails f498 [c490, c2, c340, c472] c498 unsat498 (by rfl) a
  have h0 : Entails.eval a c490 := derived490 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c472 := derived472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c499 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f499 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c490, some c2, some c6, some c495, some c497, some c1, some c299, some c329, some c260, some c328, some c498, some c112, some c212, some c261, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p499 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked499 : lratChecker f499 p499 = .success := by decide +kernel
theorem unsat499 : Unsatisfiable (PosFin 31) f499 := by
  apply lratCheckerSound f499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p499
  · intro a ha; simp [p499] at ha; subst a; trivial
  · exact checked499
theorem derived499 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c499 := by
  apply localUnsat_implies_entails f499 [c449, c490, c2, c6, c495, c497, c1, c299, c329, c260, c328, c498, c112, c212, c261] c499 unsat499 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c490 := derived490 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c495 := derived495 a h
  have h5 : Entails.eval a c497 := derived497 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c329 := h 328 (by decide)
  have h9 : Entails.eval a c260 := h 259 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c498 := derived498 a h
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c212 := h 211 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c500 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f500 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c6, some c490, some c2, some c499, some c64, some c72, some c84, some c85, some c16, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p500 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked500 : lratChecker f500 p500 = .success := by decide +kernel
theorem unsat500 : Unsatisfiable (PosFin 31) f500 := by
  apply lratCheckerSound f500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p500
  · intro a ha; simp [p500] at ha; subst a; trivial
  · exact checked500
theorem derived500 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c500 := by
  apply localUnsat_implies_entails f500 [c449, c6, c490, c2, c499, c64, c72, c84, c85, c16] c500 unsat500 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c490 := derived490 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c499 := derived499 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c501 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f501 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c490, some c500, some c67, some c451, some c294, some c156, some c257, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p501 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked501 : lratChecker f501 p501 = .success := by decide +kernel
theorem unsat501 : Unsatisfiable (PosFin 31) f501 := by
  apply lratCheckerSound f501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p501
  · intro a ha; simp [p501] at ha; subst a; trivial
  · exact checked501
theorem derived501 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c501 := by
  apply localUnsat_implies_entails f501 [c449, c490, c500, c67, c451, c294, c156, c257] c501 unsat501 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c490 := derived490 a h
  have h2 : Entails.eval a c500 := derived500 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c502 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f502 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c490, some c501, some c39, some c451, some c2, some c467, some c6, some c64, some c130, some c128, some c16, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p502 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked502 : lratChecker f502 p502 = .success := by decide +kernel
theorem unsat502 : Unsatisfiable (PosFin 31) f502 := by
  apply lratCheckerSound f502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p502
  · intro a ha; simp [p502] at ha; subst a; trivial
  · exact checked502
theorem derived502 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c502 := by
  apply localUnsat_implies_entails f502 [c449, c490, c501, c39, c451, c2, c467, c6, c64, c130, c128, c16] c502 unsat502 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c490 := derived490 a h
  have h2 : Entails.eval a c501 := derived501 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c467 := derived467 a h
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c130 := h 129 (by decide)
  have h10 : Entails.eval a c128 := h 127 (by decide)
  have h11 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c503 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f503 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c495, some c490, some c6, some c501, some c39, some c184, some c451, some c467, some c154, some c2, some c299, some c502, some c498, some c49, some c212, some c261, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p503 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked503 : lratChecker f503 p503 = .success := by decide +kernel
theorem unsat503 : Unsatisfiable (PosFin 31) f503 := by
  apply lratCheckerSound f503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p503
  · intro a ha; simp [p503] at ha; subst a; trivial
  · exact checked503
theorem derived503 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c503 := by
  apply localUnsat_implies_entails f503 [c449, c495, c490, c6, c501, c39, c184, c451, c467, c154, c2, c299, c502, c498, c49, c212, c261] c503 unsat503 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c495 := derived495 a h
  have h2 : Entails.eval a c490 := derived490 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c501 := derived501 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c184 := h 183 (by decide)
  have h7 : Entails.eval a c451 := derived451 a h
  have h8 : Entails.eval a c467 := derived467 a h
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c502 := derived502 a h
  have h13 : Entails.eval a c498 := derived498 a h
  have h14 : Entails.eval a c49 := h 48 (by decide)
  have h15 : Entails.eval a c212 := h 211 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c504 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f504 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c40, some c184, some c259, some c226, some c328, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p504 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked504 : lratChecker f504 p504 = .success := by decide +kernel
theorem unsat504 : Unsatisfiable (PosFin 31) f504 := by
  apply lratCheckerSound f504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p504
  · intro a ha; simp [p504] at ha; subst a; trivial
  · exact checked504
theorem derived504 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c504 := by
  apply localUnsat_implies_entails f504 [c449, c40, c184, c259, c226, c328] c504 unsat504 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c226 := h 225 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c505 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c490, some c495, some c503, some c504, some c294, some c324, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p505 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 31) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c449, c490, c495, c503, c504, c294, c324] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c490 := derived490 a h
  have h2 : Entails.eval a c495 := derived495 a h
  have h3 : Entails.eval a c503 := derived503 a h
  have h4 : Entails.eval a c504 := derived504 a h
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c294, some c324, some c255, some c259, some c158, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p506 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 31) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c449, c294, c324, c255, c259, c158] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c294 := h 293 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1, some c506, some c505, some c220, some c234, some c27, some c134, some c57, some c176, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p507 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 31) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c1, c506, c505, c220, c234, c27, c134, c57, c176] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c505 := derived505 a h
  have h3 : Entails.eval a c220 := h 219 (by decide)
  have h4 : Entails.eval a c234 := h 233 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c506, some c185, some c224, some c327, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p508 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 31) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c449, c506, c185, c224, c327] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c185 := h 184 (by decide)
  have h3 : Entails.eval a c224 := h 223 (by decide)
  have h4 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c1, some c508, some c507, some c506, some c505, some c71, some c258, some c156, some c136, some c120, some c49, some c412, some c58, some c12, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p509 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 31) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c449, c1, c508, c507, c506, c505, c71, c258, c156, c136, c120, c49, c412, c58, c12] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c507 := derived507 a h
  have h4 : Entails.eval a c506 := derived506 a h
  have h5 : Entails.eval a c505 := derived505 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c412 := derived412 a h
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c510 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c1, some c508, some c507, some c506, some c505, some c57, some c176, some c219, some c27, some c56, some c247, some c146, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p510 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 31) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c449, c1, c508, c507, c506, c505, c57, c176, c219, c27, c56, c247, c146] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c507 := derived507 a h
  have h4 : Entails.eval a c506 := derived506 a h
  have h5 : Entails.eval a c505 := derived505 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c176 := h 175 (by decide)
  have h8 : Entails.eval a c219 := h 218 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c1, some c508, some c507, some c506, some c505, some c510, some c303, some c176, some c252, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p511 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 31) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c449, c1, c508, c507, c506, c505, c510, c303, c176, c252] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c507 := derived507 a h
  have h4 : Entails.eval a c506 := derived506 a h
  have h5 : Entails.eval a c505 := derived505 a h
  have h6 : Entails.eval a c510 := derived510 a h
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c505, some c511, some c134, some c13, some c509, some c8, some c120, some c412, some c5, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p512 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 31) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c505, c511, c134, c13, c509, c8, c120, c412, c5] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c509 := derived509 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c412 := derived412 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c505, some c1, some c508, some c507, some c511, some c512, some c57, some c145, some c219, some c214, some c48, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p513 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 31) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c449, c505, c1, c508, c507, c511, c512, c57, c145, c219, c214, c48] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c505 := derived505 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c508 := derived508 a h
  have h4 : Entails.eval a c507 := derived507 a h
  have h5 : Entails.eval a c511 := derived511 a h
  have h6 : Entails.eval a c512 := derived512 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c214 := h 213 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c514 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f514 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c504, some c489, some c26, some c13, some c133, some c137, some c49, some c478, some c24, some c29, some c47, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p514 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked514 : lratChecker f514 p514 = .success := by decide +kernel
theorem unsat514 : Unsatisfiable (PosFin 31) f514 := by
  apply lratCheckerSound f514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p514
  · intro a ha; simp [p514] at ha; subst a; trivial
  · exact checked514
theorem derived514 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c514 := by
  apply localUnsat_implies_entails f514 [c504, c489, c26, c13, c133, c137, c49, c478, c24, c29, c47] c514 unsat514 (by rfl) a
  have h0 : Entails.eval a c504 := derived504 a h
  have h1 : Entails.eval a c489 := derived489 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c137 := h 136 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c478 := derived478 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c515 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, false), (⟨13, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f515 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c145, some c214, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p515 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked515 : lratChecker f515 p515 = .success := by decide +kernel
theorem unsat515 : Unsatisfiable (PosFin 31) f515 := by
  apply lratCheckerSound f515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p515
  · intro a ha; simp [p515] at ha; subst a; trivial
  · exact checked515
theorem derived515 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c515 := by
  apply localUnsat_implies_entails f515 [c145, c214] c515 unsat515 (by rfl) a
  have h0 : Entails.eval a c145 := h 144 (by decide)
  have h1 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c516 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f516 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c504, some c489, some c71, some c58, some c133, some c121, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p516 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked516 : lratChecker f516 p516 = .success := by decide +kernel
theorem unsat516 : Unsatisfiable (PosFin 31) f516 := by
  apply lratCheckerSound f516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p516
  · intro a ha; simp [p516] at ha; subst a; trivial
  · exact checked516
theorem derived516 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c516 := by
  apply localUnsat_implies_entails f516 [c504, c489, c71, c58, c133, c121] c516 unsat516 (by rfl) a
  have h0 : Entails.eval a c504 := derived504 a h
  have h1 : Entails.eval a c489 := derived489 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c517 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f517 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c513, some c504, some c489, some c505, some c514, some c516, some c478, some c29, some c262, some c244, some c275, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p517 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked517 : lratChecker f517 p517 = .success := by decide +kernel
theorem unsat517 : Unsatisfiable (PosFin 31) f517 := by
  apply lratCheckerSound f517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p517
  · intro a ha; simp [p517] at ha; subst a; trivial
  · exact checked517
theorem derived517 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c517 := by
  apply localUnsat_implies_entails f517 [c513, c504, c489, c505, c514, c516, c478, c29, c262, c244, c275] c517 unsat517 (by rfl) a
  have h0 : Entails.eval a c513 := derived513 a h
  have h1 : Entails.eval a c504 := derived504 a h
  have h2 : Entails.eval a c489 := derived489 a h
  have h3 : Entails.eval a c505 := derived505 a h
  have h4 : Entails.eval a c514 := derived514 a h
  have h5 : Entails.eval a c516 := derived516 a h
  have h6 : Entails.eval a c478 := derived478 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c262 := h 261 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c518 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f518 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c505, some c513, some c504, some c489, some c517, some c8, some c26, some c13, some c412, some c137, some c271, some c49, some c478, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p518 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked518 : lratChecker f518 p518 = .success := by decide +kernel
theorem unsat518 : Unsatisfiable (PosFin 31) f518 := by
  apply lratCheckerSound f518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p518
  · intro a ha; simp [p518] at ha; subst a; trivial
  · exact checked518
theorem derived518 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c518 := by
  apply localUnsat_implies_entails f518 [c505, c513, c504, c489, c517, c8, c26, c13, c412, c137, c271, c49, c478] c518 unsat518 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c513 := derived513 a h
  have h2 : Entails.eval a c504 := derived504 a h
  have h3 : Entails.eval a c489 := derived489 a h
  have h4 : Entails.eval a c517 := derived517 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c412 := derived412 a h
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c478 := derived478 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c519 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨29, by decide⟩, false), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c8, some c478, some c24, some c271, some c277, some c249, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p519 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 31) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c8, c478, c24, c271, c277, c249] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c478 := derived478 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c8, some c518, some c6, some c451, some c24, some c2, some c299, some c269, some c143, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p520 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 31) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c449, c8, c518, c6, c451, c24, c2, c299, c269, c143] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c518 := derived518 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c518, some c519, some c520, some c157, some c229, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p521 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 31) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c518, c519, c520, c157, c229] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c520 := derived520 a h
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c522 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c493, some c489, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p522 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 31) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c493, c489] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c489 := derived489 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c523 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c258, some c327, some c157, some c37, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p523 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 31) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c449, c258, c327, c157, c37] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c327 := h 326 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c524 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c518, some c522, some c521, some c523, some c8, some c49, some c157, some c39, some c156, some c48, some c257, some c269, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p524 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 31) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c449, c518, c522, c521, c523, c8, c49, c157, c39, c156, c48, c257, c269] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c518 := derived518 a h
  have h2 : Entails.eval a c522 := derived522 a h
  have h3 : Entails.eval a c521 := derived521 a h
  have h4 : Entails.eval a c523 := derived523 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c156 := h 155 (by decide)
  have h10 : Entails.eval a c48 := h 47 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c525 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c522, some c518, some c8, some c521, some c49, some c523, some c524, some c451, some c24, some c269, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p525 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 31) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c522, c518, c8, c521, c49, c523, c524, c451, c24, c269] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c522 := derived522 a h
  have h1 : Entails.eval a c518 := derived518 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c521 := derived521 a h
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c523 := derived523 a h
  have h6 : Entails.eval a c524 := derived524 a h
  have h7 : Entails.eval a c451 := derived451 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c518, some c6, some c525, some c133, some c522, some c505, some c58, some c12, some c49, some c515, some c29, some c57, some c39, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p526 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 31) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c449, c518, c6, c525, c133, c522, c505, c58, c12, c49, c515, c29, c57, c39] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c518 := derived518 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c525 := derived525 a h
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c522 := derived522 a h
  have h6 : Entails.eval a c505 := derived505 a h
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c515 := derived515 a h
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c157, some c229, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p527 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 31) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c157, c229] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c157 := h 156 (by decide)
  have h1 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c528 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c525, some c518, some c522, some c526, some c527, some c29, some c6, some c133, some c505, some c451, some c2, some c299, some c190, some c471, some c239, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p528 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 31) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c449, c525, c518, c522, c526, c527, c29, c6, c133, c505, c451, c2, c299, c190, c471, c239] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c525 := derived525 a h
  have h2 : Entails.eval a c518 := derived518 a h
  have h3 : Entails.eval a c522 := derived522 a h
  have h4 : Entails.eval a c526 := derived526 a h
  have h5 : Entails.eval a c527 := derived527 a h
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c505 := derived505 a h
  have h10 : Entails.eval a c451 := derived451 a h
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c471 := derived471 a h
  have h15 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c518, some c6, some c505, some c522, some c525, some c133, some c526, some c527, some c225, some c29, some c528, some c41, some c240, some c76, some c111, some c210, some c164, some c214, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p529 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 31) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c449, c518, c6, c505, c522, c525, c133, c526, c527, c225, c29, c528, c41, c240, c76, c111, c210, c164, c214] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c518 := derived518 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c505 := derived505 a h
  have h4 : Entails.eval a c522 := derived522 a h
  have h5 : Entails.eval a c525 := derived525 a h
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c526 := derived526 a h
  have h8 : Entails.eval a c527 := derived527 a h
  have h9 : Entails.eval a c225 := h 224 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c528 := derived528 a h
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c240 := h 239 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c111 := h 110 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c529, some c1, some c518, some c523, some c294, some c324, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p530 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 31) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c449, c529, c1, c518, c523, c294, c324] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c529 := derived529 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c518 := derived518 a h
  have h4 : Entails.eval a c523 := derived523 a h
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c529, some c294, some c505, some c530, some c255, some c220, some c134, some c67, some c190, some c267, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p531 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 31) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c449, c529, c294, c505, c530, c255, c220, c134, c67, c190, c267] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c529 := derived529 a h
  have h2 : Entails.eval a c294 := h 293 (by decide)
  have h3 : Entails.eval a c505 := derived505 a h
  have h4 : Entails.eval a c530 := derived530 a h
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c220 := h 219 (by decide)
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c529, some c1, some c518, some c6, some c90, some c412, some c8, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p532 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 31) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c449, c529, c1, c518, c6, c90, c412, c8] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c529 := derived529 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c518 := derived518 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c412 := derived412 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c530, some c518, some c532, some c531, some c529, some c1, some c486, some c228, some c41, some c187, some c5, some c268, some c333, some c266, some c202, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p533 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 31) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c530, c518, c532, c531, c529, c1, c486, c228, c41, c187, c5, c268, c333, c266, c202] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c518 := derived518 a h
  have h2 : Entails.eval a c532 := derived532 a h
  have h3 : Entails.eval a c531 := derived531 a h
  have h4 : Entails.eval a c529 := derived529 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c486 := derived486 a h
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c505, some c518, some c529, some c1, some c530, some c532, some c5, some c531, some c486, some c228, some c41, some c187, some c67, some c533, some c57, some c331, some c123, some c165, some c341, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p534 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 31) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c505, c518, c529, c1, c530, c532, c5, c531, c486, c228, c41, c187, c67, c533, c57, c331, c123, c165, c341] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c518 := derived518 a h
  have h2 : Entails.eval a c529 := derived529 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c530 := derived530 a h
  have h5 : Entails.eval a c532 := derived532 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c531 := derived531 a h
  have h8 : Entails.eval a c486 := derived486 a h
  have h9 : Entails.eval a c228 := h 227 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c533 := derived533 a h
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c331 := h 330 (by decide)
  have h16 : Entails.eval a c123 := h 122 (by decide)
  have h17 : Entails.eval a c165 := h 164 (by decide)
  have h18 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c534, some c5, some c74, some c140, some c200, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p535 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 31) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c534, c5, c74, c140, c200] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c534 := derived534 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c67, some c535, some c523, some c258, some c188, some c156, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p536 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 31) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c449, c67, c535, c523, c258, c188, c156] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c535 := derived535 a h
  have h3 : Entails.eval a c523 := derived523 a h
  have h4 : Entails.eval a c258 := h 257 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c523, some c258, some c508, some c454, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p537 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 31) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c523, c258, c508, c454] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c523 := derived523 a h
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c454 := derived454 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨28, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c185, some c486, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p538 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 31) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c185, c486] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c486 := derived486 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c539 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨8, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c537, some c538, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p539 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 31) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c537, c538] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c538 := derived538 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c540 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c536, some c539, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p540 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 31) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c536, c539] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c536 := derived536 a h
  have h1 : Entails.eval a c539 := derived539 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c541 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c538, some c523, some c58, some c508, some c121, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p541 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 31) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c538, c523, c58, c508, c121] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c538 := derived538 a h
  have h1 : Entails.eval a c523 := derived523 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c508 := derived508 a h
  have h4 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨17, by decide⟩, false), (⟨22, by decide⟩, true), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c534, some c449, some c359, some c58, some c49, some c203, some c244, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p542 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 31) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c534, c449, c359, c58, c49, c203, c244] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c534 := derived534 a h
  have h1 : Entails.eval a c449 := derived449 a h
  have h2 : Entails.eval a c359 := derived359 a h
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived542

end CochromaticTwenty.Certificates.Z12Direct_5_7_13
