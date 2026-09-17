import MerLeanExperiment.Certificates.B16_3_1.Steps0000_0099

/-! Generated from the actual pinned b16_3_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c481 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨23, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨51, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c79, some c470, some c359, some c329, some c221, some c307, some c232, some c350, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked481 : lratChecker f481 p481 = .success := by decide +kernel
theorem unsat481 : Unsatisfiable (PosFin 57) f481 := by
  apply lratCheckerSound f481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p481
  · intro a ha; simp [p481] at ha; subst a; trivial
  · exact checked481
theorem derived481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c481 := by
  apply localUnsat_implies_entails f481 [c61, c79, c470, c359, c329, c221, c307, c232, c350] c481 unsat481 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c470 := derived470 a h
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c482 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c476, some c61, some c79, some c473, some c471, some c465, some c457, some c436, some c477, some c480, some c234, some c130, some c16, some c481, some c351, some c358, some c307, some c166, some c329, some c63, some c337, some c12, some c328, some c152, some c179, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked482 : lratChecker f482 p482 = .success := by decide +kernel
theorem unsat482 : Unsatisfiable (PosFin 57) f482 := by
  apply lratCheckerSound f482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p482
  · intro a ha; simp [p482] at ha; subst a; trivial
  · exact checked482
theorem derived482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c482 := by
  apply localUnsat_implies_entails f482 [c476, c61, c79, c473, c471, c465, c457, c436, c477, c480, c234, c130, c16, c481, c351, c358, c307, c166, c329, c63, c337, c12, c328, c152, c179] c482 unsat482 (by rfl) a
  have h0 : Entails.eval a c476 := derived476 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c473 := derived473 a h
  have h4 : Entails.eval a c471 := derived471 a h
  have h5 : Entails.eval a c465 := derived465 a h
  have h6 : Entails.eval a c457 := derived457 a h
  have h7 : Entails.eval a c436 := derived436 a h
  have h8 : Entails.eval a c477 := derived477 a h
  have h9 : Entails.eval a c480 := derived480 a h
  have h10 : Entails.eval a c234 := h 233 (by decide)
  have h11 : Entails.eval a c130 := h 129 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c481 := derived481 a h
  have h14 : Entails.eval a c351 := h 350 (by decide)
  have h15 : Entails.eval a c358 := h 357 (by decide)
  have h16 : Entails.eval a c307 := h 306 (by decide)
  have h17 : Entails.eval a c166 := h 165 (by decide)
  have h18 : Entails.eval a c329 := h 328 (by decide)
  have h19 : Entails.eval a c63 := h 62 (by decide)
  have h20 : Entails.eval a c337 := h 336 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c328 := h 327 (by decide)
  have h23 : Entails.eval a c152 := h 151 (by decide)
  have h24 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c483 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c457, some c473, some c476, some c79, some c61, some c482, some c116, some c115, some c92, some c464, some c308, some c380, some c64, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked483 : lratChecker f483 p483 = .success := by decide +kernel
theorem unsat483 : Unsatisfiable (PosFin 57) f483 := by
  apply lratCheckerSound f483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p483
  · intro a ha; simp [p483] at ha; subst a; trivial
  · exact checked483
theorem derived483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c483 := by
  apply localUnsat_implies_entails f483 [c457, c473, c476, c79, c61, c482, c116, c115, c92, c464, c308, c380, c64] c483 unsat483 (by rfl) a
  have h0 : Entails.eval a c457 := derived457 a h
  have h1 : Entails.eval a c473 := derived473 a h
  have h2 : Entails.eval a c476 := derived476 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c482 := derived482 a h
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c464 := derived464 a h
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c484 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c116, some c115, some c96, some c92, some c100, some c64, some c117, some c308, some c94, some c70, some c320, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked484 : lratChecker f484 p484 = .success := by decide +kernel
theorem unsat484 : Unsatisfiable (PosFin 57) f484 := by
  apply lratCheckerSound f484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p484
  · intro a ha; simp [p484] at ha; subst a; trivial
  · exact checked484
theorem derived484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c484 := by
  apply localUnsat_implies_entails f484 [c382, c116, c115, c96, c92, c100, c64, c117, c308, c94, c70, c320] c484 unsat484 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c308 := h 307 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c485 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨52, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c484, some c66, some c84, some c101, some c309, some c113, some c43, some c31, some c264, some c281, some c22, some c49, some c215, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked485 : lratChecker f485 p485 = .success := by decide +kernel
theorem unsat485 : Unsatisfiable (PosFin 57) f485 := by
  apply lratCheckerSound f485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p485
  · intro a ha; simp [p485] at ha; subst a; trivial
  · exact checked485
theorem derived485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c485 := by
  apply localUnsat_implies_entails f485 [c484, c66, c84, c101, c309, c113, c43, c31, c264, c281, c22, c49, c215] c485 unsat485 (by rfl) a
  have h0 : Entails.eval a c484 := derived484 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c281 := h 280 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c486 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c485, some c25, some c229, some c31, some c113, some c116, some c101, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked486 : lratChecker f486 p486 = .success := by decide +kernel
theorem unsat486 : Unsatisfiable (PosFin 57) f486 := by
  apply lratCheckerSound f486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p486
  · intro a ha; simp [p486] at ha; subst a; trivial
  · exact checked486
theorem derived486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c486 := by
  apply localUnsat_implies_entails f486 [c485, c25, c229, c31, c113, c116, c101] c486 unsat486 (by rfl) a
  have h0 : Entails.eval a c485 := derived485 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c487 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, false), (⟨21, by decide⟩, false), (⟨24, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c117, some c35, some c24, some c248, some c282, some c127, some c121, some c51, some c266, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked487 : lratChecker f487 p487 = .success := by decide +kernel
theorem unsat487 : Unsatisfiable (PosFin 57) f487 := by
  apply lratCheckerSound f487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p487
  · intro a ha; simp [p487] at ha; subst a; trivial
  · exact checked487
theorem derived487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c487 := by
  apply localUnsat_implies_entails f487 [c12, c117, c35, c24, c248, c282, c127, c121, c51, c266] c487 unsat487 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c248 := h 247 (by decide)
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c488 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c436, some c457, some c465, some c483, some c372, some c486, some c87, some c25, some c393, some c229, some c230, some c223, some c88, some c130, some c31, some c225, some c487, some c81, some c100, some c63, some c118, some c312, some c319, some c71, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked488 : lratChecker f488 p488 = .success := by decide +kernel
theorem unsat488 : Unsatisfiable (PosFin 57) f488 := by
  apply lratCheckerSound f488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p488
  · intro a ha; simp [p488] at ha; subst a; trivial
  · exact checked488
theorem derived488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c488 := by
  apply localUnsat_implies_entails f488 [c436, c457, c465, c483, c372, c486, c87, c25, c393, c229, c230, c223, c88, c130, c31, c225, c487, c81, c100, c63, c118, c312, c319, c71] c488 unsat488 (by rfl) a
  have h0 : Entails.eval a c436 := derived436 a h
  have h1 : Entails.eval a c457 := derived457 a h
  have h2 : Entails.eval a c465 := derived465 a h
  have h3 : Entails.eval a c483 := derived483 a h
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c486 := derived486 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c393 := derived393 a h
  have h9 : Entails.eval a c229 := h 228 (by decide)
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c223 := h 222 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c130 := h 129 (by decide)
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c225 := h 224 (by decide)
  have h16 : Entails.eval a c487 := derived487 a h
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c100 := h 99 (by decide)
  have h19 : Entails.eval a c63 := h 62 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  have h21 : Entails.eval a c312 := h 311 (by decide)
  have h22 : Entails.eval a c319 := h 318 (by decide)
  have h23 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c489 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c81, some c63, some c307, some c43, some c69, some c262, some c312, some c19, some c26, some c203, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked489 : lratChecker f489 p489 = .success := by decide +kernel
theorem unsat489 : Unsatisfiable (PosFin 57) f489 := by
  apply lratCheckerSound f489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p489
  · intro a ha; simp [p489] at ha; subst a; trivial
  · exact checked489
theorem derived489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c489 := by
  apply localUnsat_implies_entails f489 [c81, c63, c307, c43, c69, c262, c312, c19, c26, c203] c489 unsat489 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c490 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c465, some c436, some c457, some c483, some c372, some c486, some c488, some c489, some c382, some c80, some c26, some c89, some c234, some c117, some c225, some c230, some c17, some c34, some c281, some c254, some c221, some c193, some c263, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked490 : lratChecker f490 p490 = .success := by decide +kernel
theorem unsat490 : Unsatisfiable (PosFin 57) f490 := by
  apply lratCheckerSound f490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p490
  · intro a ha; simp [p490] at ha; subst a; trivial
  · exact checked490
theorem derived490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c490 := by
  apply localUnsat_implies_entails f490 [c465, c436, c457, c483, c372, c486, c488, c489, c382, c80, c26, c89, c234, c117, c225, c230, c17, c34, c281, c254, c221, c193, c263] c490 unsat490 (by rfl) a
  have h0 : Entails.eval a c465 := derived465 a h
  have h1 : Entails.eval a c436 := derived436 a h
  have h2 : Entails.eval a c457 := derived457 a h
  have h3 : Entails.eval a c483 := derived483 a h
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c486 := derived486 a h
  have h6 : Entails.eval a c488 := derived488 a h
  have h7 : Entails.eval a c489 := derived489 a h
  have h8 : Entails.eval a c382 := derived382 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c234 := h 233 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c225 := h 224 (by decide)
  have h15 : Entails.eval a c230 := h 229 (by decide)
  have h16 : Entails.eval a c17 := h 16 (by decide)
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c281 := h 280 (by decide)
  have h19 : Entails.eval a c254 := h 253 (by decide)
  have h20 : Entails.eval a c221 := h 220 (by decide)
  have h21 : Entails.eval a c193 := h 192 (by decide)
  have h22 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c491 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c483, some c372, some c465, some c490, some c393, some c488, some c382, some c457, some c436, some c225, some c223, some c241, some c254, some c353, some c221, some c359, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked491 : lratChecker f491 p491 = .success := by decide +kernel
theorem unsat491 : Unsatisfiable (PosFin 57) f491 := by
  apply lratCheckerSound f491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p491
  · intro a ha; simp [p491] at ha; subst a; trivial
  · exact checked491
theorem derived491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c491 := by
  apply localUnsat_implies_entails f491 [c483, c372, c465, c490, c393, c488, c382, c457, c436, c225, c223, c241, c254, c353, c221, c359] c491 unsat491 (by rfl) a
  have h0 : Entails.eval a c483 := derived483 a h
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c465 := derived465 a h
  have h3 : Entails.eval a c490 := derived490 a h
  have h4 : Entails.eval a c393 := derived393 a h
  have h5 : Entails.eval a c488 := derived488 a h
  have h6 : Entails.eval a c382 := derived382 a h
  have h7 : Entails.eval a c457 := derived457 a h
  have h8 : Entails.eval a c436 := derived436 a h
  have h9 : Entails.eval a c225 := h 224 (by decide)
  have h10 : Entails.eval a c223 := h 222 (by decide)
  have h11 : Entails.eval a c241 := h 240 (by decide)
  have h12 : Entails.eval a c254 := h 253 (by decide)
  have h13 : Entails.eval a c353 := h 352 (by decide)
  have h14 : Entails.eval a c221 := h 220 (by decide)
  have h15 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c492 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨39, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c281, some c49, some c143, some c12, some c127, some c121, some c262, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked492 : lratChecker f492 p492 = .success := by decide +kernel
theorem unsat492 : Unsatisfiable (PosFin 57) f492 := by
  apply lratCheckerSound f492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p492
  · intro a ha; simp [p492] at ha; subst a; trivial
  · exact checked492
theorem derived492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c492 := by
  apply localUnsat_implies_entails f492 [c281, c49, c143, c12, c127, c121, c262] c492 unsat492 (by rfl) a
  have h0 : Entails.eval a c281 := h 280 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c143 := h 142 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c493 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c483, some c372, some c465, some c457, some c436, some c486, some c488, some c489, some c491, some c229, some c17, some c33, some c249, some c234, some c492, some c62, some c207, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked493 : lratChecker f493 p493 = .success := by decide +kernel
theorem unsat493 : Unsatisfiable (PosFin 57) f493 := by
  apply lratCheckerSound f493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p493
  · intro a ha; simp [p493] at ha; subst a; trivial
  · exact checked493
theorem derived493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c493 := by
  apply localUnsat_implies_entails f493 [c483, c372, c465, c457, c436, c486, c488, c489, c491, c229, c17, c33, c249, c234, c492, c62, c207] c493 unsat493 (by rfl) a
  have h0 : Entails.eval a c483 := derived483 a h
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c465 := derived465 a h
  have h3 : Entails.eval a c457 := derived457 a h
  have h4 : Entails.eval a c436 := derived436 a h
  have h5 : Entails.eval a c486 := derived486 a h
  have h6 : Entails.eval a c488 := derived488 a h
  have h7 : Entails.eval a c489 := derived489 a h
  have h8 : Entails.eval a c491 := derived491 a h
  have h9 : Entails.eval a c229 := h 228 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c234 := h 233 (by decide)
  have h14 : Entails.eval a c492 := derived492 a h
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c494 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨48, by decide⟩, true), (⟨1, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c107, some c96, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked494 : lratChecker f494 p494 = .success := by decide +kernel
theorem unsat494 : Unsatisfiable (PosFin 57) f494 := by
  apply lratCheckerSound f494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p494
  · intro a ha; simp [p494] at ha; subst a; trivial
  · exact checked494
theorem derived494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c494 := by
  apply localUnsat_implies_entails f494 [c108, c107, c96] c494 unsat494 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c495 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c100, some c109, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked495 : lratChecker f495 p495 = .success := by decide +kernel
theorem unsat495 : Unsatisfiable (PosFin 57) f495 := by
  apply lratCheckerSound f495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p495
  · intro a ha; simp [p495] at ha; subst a; trivial
  · exact checked495
theorem derived495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c495 := by
  apply localUnsat_implies_entails f495 [c101, c100, c109] c495 unsat495 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c496 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨17, by decide⟩, true), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨47, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c125, some c107, some c31, some c494, some c109, some c2, some c84, some c163, some c365, some c368, some c216, some c385, some c234, some c80, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked496 : lratChecker f496 p496 = .success := by decide +kernel
theorem unsat496 : Unsatisfiable (PosFin 57) f496 := by
  apply lratCheckerSound f496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p496
  · intro a ha; simp [p496] at ha; subst a; trivial
  · exact checked496
theorem derived496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c496 := by
  apply localUnsat_implies_entails f496 [c125, c107, c31, c494, c109, c2, c84, c163, c365, c368, c216, c385, c234, c80] c496 unsat496 (by rfl) a
  have h0 : Entails.eval a c125 := h 124 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c494 := derived494 a h
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  have h8 : Entails.eval a c365 := h 364 (by decide)
  have h9 : Entails.eval a c368 := h 367 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c385 := derived385 a h
  have h12 : Entails.eval a c234 := h 233 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c497 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c436, some c457, some c465, some c483, some c372, some c493, some c495, some c108, some c107, some c494, some c31, some c382, some c229, some c125, some c171, some c496, some c92, some c64, some c444, some c467, some c322, some c234, some c71, some c26, some c313, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked497 : lratChecker f497 p497 = .success := by decide +kernel
theorem unsat497 : Unsatisfiable (PosFin 57) f497 := by
  apply lratCheckerSound f497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p497
  · intro a ha; simp [p497] at ha; subst a; trivial
  · exact checked497
theorem derived497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c497 := by
  apply localUnsat_implies_entails f497 [c436, c457, c465, c483, c372, c493, c495, c108, c107, c494, c31, c382, c229, c125, c171, c496, c92, c64, c444, c467, c322, c234, c71, c26, c313] c497 unsat497 (by rfl) a
  have h0 : Entails.eval a c436 := derived436 a h
  have h1 : Entails.eval a c457 := derived457 a h
  have h2 : Entails.eval a c465 := derived465 a h
  have h3 : Entails.eval a c483 := derived483 a h
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c493 := derived493 a h
  have h6 : Entails.eval a c495 := derived495 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c494 := derived494 a h
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c382 := derived382 a h
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c125 := h 124 (by decide)
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c496 := derived496 a h
  have h16 : Entails.eval a c92 := h 91 (by decide)
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c444 := derived444 a h
  have h19 : Entails.eval a c467 := derived467 a h
  have h20 : Entails.eval a c322 := h 321 (by decide)
  have h21 : Entails.eval a c234 := h 233 (by decide)
  have h22 : Entails.eval a c71 := h 70 (by decide)
  have h23 : Entails.eval a c26 := h 25 (by decide)
  have h24 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c498 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨6, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c84, some c324, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked498 : lratChecker f498 p498 = .success := by decide +kernel
theorem unsat498 : Unsatisfiable (PosFin 57) f498 := by
  apply lratCheckerSound f498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p498
  · intro a ha; simp [p498] at ha; subst a; trivial
  · exact checked498
theorem derived498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c498 := by
  apply localUnsat_implies_entails f498 [c66, c84, c324] c498 unsat498 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c499 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨42, by decide⟩, true), (⟨54, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c26, some c285, some c207, some c44, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked499 : lratChecker f499 p499 = .success := by decide +kernel
theorem unsat499 : Unsatisfiable (PosFin 57) f499 := by
  apply lratCheckerSound f499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p499
  · intro a ha; simp [p499] at ha; subst a; trivial
  · exact checked499
theorem derived499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c499 := by
  apply localUnsat_implies_entails f499 [c80, c26, c285, c207, c44] c499 unsat499 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c285 := h 284 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c500 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c67, some c85, some c498, some c324, some c366, some c48, some c277, some c60, some c23, some c499, some c112, some c104, some c58, some c293, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked500 : lratChecker f500 p500 = .success := by decide +kernel
theorem unsat500 : Unsatisfiable (PosFin 57) f500 := by
  apply lratCheckerSound f500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p500
  · intro a ha; simp [p500] at ha; subst a; trivial
  · exact checked500
theorem derived500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c500 := by
  apply localUnsat_implies_entails f500 [c497, c67, c85, c498, c324, c366, c48, c277, c60, c23, c499, c112, c104, c58, c293] c500 unsat500 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c498 := derived498 a h
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c277 := h 276 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c499 := derived499 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c501 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨48, by decide⟩, false), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c30, some c228, some c125, some c1, some c170, some c162, some c363, some c367, some c216, some c93, some c233, some c112, some c80, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked501 : lratChecker f501 p501 = .success := by decide +kernel
theorem unsat501 : Unsatisfiable (PosFin 57) f501 := by
  apply lratCheckerSound f501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p501
  · intro a ha; simp [p501] at ha; subst a; trivial
  · exact checked501
theorem derived501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c501 := by
  apply localUnsat_implies_entails f501 [c30, c228, c125, c1, c170, c162, c363, c367, c216, c93, c233, c112, c80] c501 unsat501 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c233 := h 232 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c502 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨22, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c26, some c233, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked502 : lratChecker f502 p502 = .success := by decide +kernel
theorem unsat502 : Unsatisfiable (PosFin 57) f502 := by
  apply lratCheckerSound f502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p502
  · intro a ha; simp [p502] at ha; subst a; trivial
  · exact checked502
theorem derived502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c502 := by
  apply localUnsat_implies_entails f502 [c347, c26, c233] c502 unsat502 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c503 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c498, some c502, some c316, some c62, some c44, some c269, some c285, some c23, some c48, some c215, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked503 : lratChecker f503 p503 = .success := by decide +kernel
theorem unsat503 : Unsatisfiable (PosFin 57) f503 := by
  apply lratCheckerSound f503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p503
  · intro a ha; simp [p503] at ha; subst a; trivial
  · exact checked503
theorem derived503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c503 := by
  apply localUnsat_implies_entails f503 [c498, c502, c316, c62, c44, c269, c285, c23, c48, c215] c503 unsat503 (by rfl) a
  have h0 : Entails.eval a c498 := derived498 a h
  have h1 : Entails.eval a c502 := derived502 a h
  have h2 : Entails.eval a c316 := h 315 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c285 := h 284 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c504 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨46, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c30, some c498, some c107, some c382, some c501, some c503, some c112, some c93, some c368, some c367, some c350, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked504 : lratChecker f504 p504 = .success := by decide +kernel
theorem unsat504 : Unsatisfiable (PosFin 57) f504 := by
  apply lratCheckerSound f504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p504
  · intro a ha; simp [p504] at ha; subst a; trivial
  · exact checked504
theorem derived504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c504 := by
  apply localUnsat_implies_entails f504 [c30, c498, c107, c382, c501, c503, c112, c93, c368, c367, c350] c504 unsat504 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c498 := derived498 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c382 := derived382 a h
  have h4 : Entails.eval a c501 := derived501 a h
  have h5 : Entails.eval a c503 := derived503 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c505 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c107, some c85, some c67, some c108, some c102, some c109, some c500, some c504, some c95, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 57) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c497, c107, c85, c67, c108, c102, c109, c500, c504, c95] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c500 := derived500 a h
  have h8 : Entails.eval a c504 := derived504 a h
  have h9 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c62, some c316, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 57) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c80, c62, c316] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c363, some c351, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 57) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c366, c363, c351] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c107, some c85, some c67, some c108, some c505, some c372, some c380, some c104, some c112, some c506, some c377, some c498, some c109, some c507, some c89, some c26, some c411, some c232, some c28, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 57) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c497, c107, c85, c67, c108, c505, c372, c380, c104, c112, c506, c377, c498, c109, c507, c89, c26, c411, c232, c28] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c505 := derived505 a h
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c506 := derived506 a h
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c498 := derived498 a h
  have h13 : Entails.eval a c109 := h 108 (by decide)
  have h14 : Entails.eval a c507 := derived507 a h
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c26 := h 25 (by decide)
  have h17 : Entails.eval a c411 := derived411 a h
  have h18 : Entails.eval a c232 := h 231 (by decide)
  have h19 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c26, some c411, some c232, some c28, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 57) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c89, c26, c411, c232, c28] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c411 := derived411 a h
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c510 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c506, some c377, some c498, some c109, some c509, some c316, some c44, some c269, some c284, some c56, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 57) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c506, c377, c498, c109, c509, c316, c44, c269, c284, c56] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c506 := derived506 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c498 := derived498 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c509 := derived509 a h
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c108, some c107, some c67, some c85, some c508, some c370, some c379, some c104, some c112, some c506, some c510, some c102, some c109, some c498, some c500, some c30, some c233, some c26, some c18, some c269, some c285, some c23, some c48, some c215, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 57) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c497, c108, c107, c67, c85, c508, c370, c379, c104, c112, c506, c510, c102, c109, c498, c500, c30, c233, c26, c18, c269, c285, c23, c48, c215] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c506 := derived506 a h
  have h11 : Entails.eval a c510 := derived510 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c109 := h 108 (by decide)
  have h14 : Entails.eval a c498 := derived498 a h
  have h15 : Entails.eval a c500 := derived500 a h
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c233 := h 232 (by decide)
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c269 := h 268 (by decide)
  have h21 : Entails.eval a c285 := h 284 (by decide)
  have h22 : Entails.eval a c23 := h 22 (by decide)
  have h23 : Entails.eval a c48 := h 47 (by decide)
  have h24 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c109, some c102, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 57) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c111, c109, c102] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨50, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c91, some c30, some c363, some c357, some c233, some c218, some c216, some c237, some c246, some c36, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 57) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c84, c91, c30, c363, c357, c233, c218, c216, c237, c246, c36] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c233 := h 232 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c237 := h 236 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c514 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c100, some c64, some c82, some c370, some c379, some c411, some c413, some c513, some c361, some c321, some c348, some c73, some c320, some c326, some c332, some c335, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked514 : lratChecker f514 p514 = .success := by decide +kernel
theorem unsat514 : Unsatisfiable (PosFin 57) f514 := by
  apply lratCheckerSound f514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p514
  · intro a ha; simp [p514] at ha; subst a; trivial
  · exact checked514
theorem derived514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c514 := by
  apply localUnsat_implies_entails f514 [c497, c100, c64, c82, c370, c379, c411, c413, c513, c361, c321, c348, c73, c320, c326, c332, c335] c514 unsat514 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c411 := derived411 a h
  have h7 : Entails.eval a c413 := derived413 a h
  have h8 : Entails.eval a c513 := derived513 a h
  have h9 : Entails.eval a c361 := h 360 (by decide)
  have h10 : Entails.eval a c321 := h 320 (by decide)
  have h11 : Entails.eval a c348 := h 347 (by decide)
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c320 := h 319 (by decide)
  have h14 : Entails.eval a c326 := h 325 (by decide)
  have h15 : Entails.eval a c332 := h 331 (by decide)
  have h16 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c515 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, false), (⟨42, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c32, some c89, some c237, some c114, some c19, some c27, some c65, some c289, some c270, some c50, some c21, some c214, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked515 : lratChecker f515 p515 = .success := by decide +kernel
theorem unsat515 : Unsatisfiable (PosFin 57) f515 := by
  apply lratCheckerSound f515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p515
  · intro a ha; simp [p515] at ha; subst a; trivial
  · exact checked515
theorem derived515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c515 := by
  apply localUnsat_implies_entails f515 [c379, c32, c89, c237, c114, c19, c27, c65, c289, c270, c50, c21, c214] c515 unsat515 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c237 := h 236 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c516 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨42, by decide⟩, true), (⟨41, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c370, some c379, some c348, some c515, some c367, some c27, some c237, some c231, some c24, some c26, some c276, some c114, some c47, some c407, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked516 : lratChecker f516 p516 = .success := by decide +kernel
theorem unsat516 : Unsatisfiable (PosFin 57) f516 := by
  apply lratCheckerSound f516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p516
  · intro a ha; simp [p516] at ha; subst a; trivial
  · exact checked516
theorem derived516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c516 := by
  apply localUnsat_implies_entails f516 [c370, c379, c348, c515, c367, c27, c237, c231, c24, c26, c276, c114, c47, c407] c516 unsat516 (by rfl) a
  have h0 : Entails.eval a c370 := h 369 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c348 := h 347 (by decide)
  have h3 : Entails.eval a c515 := derived515 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c237 := h 236 (by decide)
  have h7 : Entails.eval a c231 := h 230 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c407 := derived407 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c517 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c348, some c332, some c317, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked517 : lratChecker f517 p517 = .success := by decide +kernel
theorem unsat517 : Unsatisfiable (PosFin 57) f517 := by
  apply lratCheckerSound f517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p517
  · intro a ha; simp [p517] at ha; subst a; trivial
  · exact checked517
theorem derived517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c517 := by
  apply localUnsat_implies_entails f517 [c348, c332, c317] c517 unsat517 (by rfl) a
  have h0 : Entails.eval a c348 := h 347 (by decide)
  have h1 : Entails.eval a c332 := h 331 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c518 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨53, by decide⟩, false), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c317, some c32, some c89, some c241, some c114, some c39, some c75, some c233, some c321, some c212, some c126, some c128, some c7, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked518 : lratChecker f518 p518 = .success := by decide +kernel
theorem unsat518 : Unsatisfiable (PosFin 57) f518 := by
  apply lratCheckerSound f518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p518
  · intro a ha; simp [p518] at ha; subst a; trivial
  · exact checked518
theorem derived518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c518 := by
  apply localUnsat_implies_entails f518 [c367, c317, c32, c89, c241, c114, c39, c75, c233, c321, c212, c126, c128, c7] c518 unsat518 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c233 := h 232 (by decide)
  have h9 : Entails.eval a c321 := h 320 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c126 := h 125 (by decide)
  have h12 : Entails.eval a c128 := h 127 (by decide)
  have h13 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c519 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨45, by decide⟩, true), (⟨53, by decide⟩, false), (⟨42, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c89, some c241, some c114, some c29, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 57) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c32, c89, c241, c114, c29] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨36, by decide⟩, false), (⟨7, by decide⟩, false), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c318, some c319, some c50, some c77, some c272, some c343, some c55, some c71, some c277, some c285, some c143, some c140, some c10, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 57) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c318, c319, c50, c77, c272, c343, c55, c71, c277, c285, c143, c140, c10] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c318 := h 317 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c272 := h 271 (by decide)
  have h5 : Entails.eval a c343 := h 342 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c277 := h 276 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c143 := h 142 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c518, some c519, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 57) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c518, c519] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c519 := derived519 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c522 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c361, some c514, some c497, some c516, some c101, some c81, some c63, some c318, some c67, some c330, some c520, some c89, some c114, some c521, some c332, some c83, some c317, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 57) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c366, c361, c514, c497, c516, c101, c81, c63, c318, c67, c330, c520, c89, c114, c521, c332, c83, c317] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c514 := derived514 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c516 := derived516 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c330 := h 329 (by decide)
  have h11 : Entails.eval a c520 := derived520 a h
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c114 := h 113 (by decide)
  have h14 : Entails.eval a c521 := derived521 a h
  have h15 : Entails.eval a c332 := h 331 (by decide)
  have h16 : Entails.eval a c83 := h 82 (by decide)
  have h17 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c523 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨5, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c332, some c83, some c317, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 57) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c332, c83, c317] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c332 := h 331 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c524 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨53, by decide⟩, false), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c317, some c32, some c47, some c293, some c270, some c50, some c19, some c210, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 57) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c367, c317, c32, c47, c293, c270, c50, c19, c210] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c525 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c514, some c497, some c366, some c522, some c381, some c80, some c370, some c114, some c81, some c63, some c318, some c330, some c523, some c524, some c519, some c29, some c319, some c50, some c77, some c282, some c272, some c293, some c337, some c256, some c19, some c208, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 57) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c514, c497, c366, c522, c381, c80, c370, c114, c81, c63, c318, c330, c523, c524, c519, c29, c319, c50, c77, c282, c272, c293, c337, c256, c19, c208] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c514 := derived514 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c522 := derived522 a h
  have h4 : Entails.eval a c381 := derived381 a h
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c330 := h 329 (by decide)
  have h12 : Entails.eval a c523 := derived523 a h
  have h13 : Entails.eval a c524 := derived524 a h
  have h14 : Entails.eval a c519 := derived519 a h
  have h15 : Entails.eval a c29 := h 28 (by decide)
  have h16 : Entails.eval a c319 := h 318 (by decide)
  have h17 : Entails.eval a c50 := h 49 (by decide)
  have h18 : Entails.eval a c77 := h 76 (by decide)
  have h19 : Entails.eval a c282 := h 281 (by decide)
  have h20 : Entails.eval a c272 := h 271 (by decide)
  have h21 : Entails.eval a c293 := h 292 (by decide)
  have h22 : Entails.eval a c337 := h 336 (by decide)
  have h23 : Entails.eval a c256 := h 255 (by decide)
  have h24 : Entails.eval a c19 := h 18 (by decide)
  have h25 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c511, some c497, some c512, some c514, some c110, some c525, some c84, some c91, some c30, some c95, some c363, some c367, some c93, some c114, some c26, some c80, some c233, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 57) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c511, c497, c512, c514, c110, c525, c84, c91, c30, c95, c363, c367, c93, c114, c26, c80, c233] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c511 := derived511 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c512 := derived512 a h
  have h3 : Entails.eval a c514 := derived514 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c525 := derived525 a h
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c363 := h 362 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c93 := h 92 (by decide)
  have h13 : Entails.eval a c114 := h 113 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c80 := h 79 (by decide)
  have h16 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c526, some c380, some c372, some c511, some c497, some c348, some c357, some c361, some c81, some c91, some c353, some c111, some c109, some c377, some c67, some c439, some c310, some c325, some c326, some c342, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 57) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c526, c380, c372, c511, c497, c348, c357, c361, c81, c91, c353, c111, c109, c377, c67, c439, c310, c325, c326, c342] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c526 := derived526 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c511 := derived511 a h
  have h4 : Entails.eval a c497 := derived497 a h
  have h5 : Entails.eval a c348 := h 347 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c361 := h 360 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c439 := derived439 a h
  have h16 : Entails.eval a c310 := h 309 (by decide)
  have h17 : Entails.eval a c325 := h 324 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c528 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨43, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c27, some c81, some c90, some c411, some c364, some c218, some c231, some c249, some c381, some c80, some c91, some c224, some c116, some c251, some c38, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 57) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c27, c81, c90, c411, c364, c218, c231, c249, c381, c80, c91, c224, c116, c251, c38] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c411 := derived411 a h
  have h4 : Entails.eval a c364 := h 363 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c231 := h 230 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c381 := derived381 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c224 := h 223 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c527, some c526, some c380, some c372, some c511, some c81, some c27, some c237, some c528, some c109, some c110, some c91, some c361, some c366, some c381, some c516, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 57) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c527, c526, c380, c372, c511, c81, c27, c237, c528, c109, c110, c91, c361, c366, c381, c516] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c527 := derived527 a h
  have h1 : Entails.eval a c526 := derived526 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c511 := derived511 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c237 := h 236 (by decide)
  have h8 : Entails.eval a c528 := derived528 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c361 := h 360 (by decide)
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c381 := derived381 a h
  have h15 : Entails.eval a c516 := derived516 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c526, some c372, some c529, some c363, some c357, some c347, some c377, some c527, some c367, some c511, some c109, some c110, some c101, some c515, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 57) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c526, c372, c529, c363, c357, c347, c377, c527, c367, c511, c109, c110, c101, c515] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c526 := derived526 a h
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c529 := derived529 a h
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c347 := h 346 (by decide)
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c527 := derived527 a h
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c511 := derived511 a h
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c515 := derived515 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨54, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c363, some c357, some c347, some c497, some c498, some c101, some c517, some c332, some c45, some c72, some c342, some c346, some c283, some c289, some c257, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 57) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c363, c357, c347, c497, c498, c101, c517, c332, c45, c72, c342, c346, c283, c289, c257] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c363 := h 362 (by decide)
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c347 := h 346 (by decide)
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c498 := derived498 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c517 := derived517 a h
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c342 := h 341 (by decide)
  have h11 : Entails.eval a c346 := h 345 (by decide)
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c289 := h 288 (by decide)
  have h14 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true), (⟨36, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c342, some c346, some c257, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true))]
def p532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 57) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c342, c346, c257] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c342 := h 341 (by decide)
  have h1 : Entails.eval a c346 := h 345 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c511, some c497, some c526, some c372, some c380, some c529, some c363, some c357, some c347, some c377, some c530, some c531, some c111, some c67, some c318, some c63, some c45, some c72, some c283, some c289, some c532, some c326, some c331, some c337, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 57) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c511, c497, c526, c372, c380, c529, c363, c357, c347, c377, c530, c531, c111, c67, c318, c63, c45, c72, c283, c289, c532, c326, c331, c337] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c511 := derived511 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c526 := derived526 a h
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c529 := derived529 a h
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c357 := h 356 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c530 := derived530 a h
  have h11 : Entails.eval a c531 := derived531 a h
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c283 := h 282 (by decide)
  have h19 : Entails.eval a c289 := h 288 (by decide)
  have h20 : Entails.eval a c532 := derived532 a h
  have h21 : Entails.eval a c326 := h 325 (by decide)
  have h22 : Entails.eval a c331 := h 330 (by decide)
  have h23 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c326, some c332, some c339, some c335, some c73, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 57) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c326, c332, c339, c335, c73] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c326 := h 325 (by decide)
  have h1 : Entails.eval a c332 := h 331 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨50, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c72, some c283, some c289, some c532, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 57) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c45, c72, c283, c289, c532] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c532 := derived532 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c511, some c533, some c85, some c111, some c370, some c379, some c534, some c354, some c535, some c317, some c27, some c91, some c90, some c237, some c231, some c365, some c411, some c218, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 57) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c497, c511, c533, c85, c111, c370, c379, c534, c354, c535, c317, c27, c91, c90, c237, c231, c365, c411, c218] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c533 := derived533 a h
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c534 := derived534 a h
  have h8 : Entails.eval a c354 := h 353 (by decide)
  have h9 : Entails.eval a c535 := derived535 a h
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c237 := h 236 (by decide)
  have h15 : Entails.eval a c231 := h 230 (by decide)
  have h16 : Entails.eval a c365 := h 364 (by decide)
  have h17 : Entails.eval a c411 := derived411 a h
  have h18 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c91, some c90, some c410, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 57) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c91, c90, c410] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c410 := derived410 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c533, some c85, some c111, some c511, some c370, some c379, some c354, some c534, some c536, some c537, some c317, some c73, some c72, some c343, some c337, some c325, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 57) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c497, c533, c85, c111, c511, c370, c379, c354, c534, c536, c537, c317, c73, c72, c343, c337, c325] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c533 := derived533 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c511 := derived511 a h
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c534 := derived534 a h
  have h9 : Entails.eval a c536 := derived536 a h
  have h10 : Entails.eval a c537 := derived537 a h
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c337 := h 336 (by decide)
  have h16 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c533, some c85, some c111, some c511, some c538, some c101, some c81, some c63, some c100, some c371, some c380, some c354, some c534, some c317, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 57) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c497, c533, c85, c111, c511, c538, c101, c81, c63, c100, c371, c380, c354, c534, c317] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c533 := derived533 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c511 := derived511 a h
  have h5 : Entails.eval a c538 := derived538 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c534 := derived534 a h
  have h14 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c511, some c63, some c81, some c539, some c110, some c533, some c497, some c317, some c340, some c345, some c354, some c50, some c71, some c380, some c293, some c114, some c352, some c386, some c21, some c365, some c208, some c519, some c19, some c272, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 57) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c511, c63, c81, c539, c110, c533, c497, c317, c340, c345, c354, c50, c71, c380, c293, c114, c352, c386, c21, c365, c208, c519, c19, c272] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c511 := derived511 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c533 := derived533 a h
  have h6 : Entails.eval a c497 := derived497 a h
  have h7 : Entails.eval a c317 := h 316 (by decide)
  have h8 : Entails.eval a c340 := h 339 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c293 := h 292 (by decide)
  have h15 : Entails.eval a c114 := h 113 (by decide)
  have h16 : Entails.eval a c352 := h 351 (by decide)
  have h17 : Entails.eval a c386 := derived386 a h
  have h18 : Entails.eval a c21 := h 20 (by decide)
  have h19 : Entails.eval a c365 := h 364 (by decide)
  have h20 : Entails.eval a c208 := h 207 (by decide)
  have h21 : Entails.eval a c519 := derived519 a h
  have h22 : Entails.eval a c19 := h 18 (by decide)
  have h23 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨34, by decide⟩, true), (⟨53, by decide⟩, false), (⟨37, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c539, some c110, some c50, some c71, some c293, some c114, some c47, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 57) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c539, c110, c50, c71, c293, c114, c47] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c539 := derived539 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨45, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c533, some c354, some c380, some c352, some c539, some c110, some c85, some c111, some c519, some c95, some c365, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 57) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c497, c533, c354, c380, c352, c539, c110, c85, c111, c519, c95, c365] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c533 := derived533 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c539 := derived539 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c519 := derived519 a h
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c540, some c511, some c63, some c81, some c539, some c110, some c497, some c533, some c85, some c111, some c354, some c380, some c542, some c319, some c77, some c541, some c344, some c343, some c330, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 57) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c540, c511, c63, c81, c539, c110, c497, c533, c85, c111, c354, c380, c542, c319, c77, c541, c344, c343, c330] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c540 := derived540 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c539 := derived539 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c497 := derived497 a h
  have h7 : Entails.eval a c533 := derived533 a h
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c542 := derived542 a h
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c77 := h 76 (by decide)
  have h15 : Entails.eval a c541 := derived541 a h
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c343 := h 342 (by decide)
  have h18 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c539, some c110, some c511, some c81, some c63, some c540, some c543, some c362, some c367, some c89, some c114, some c65, some c524, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 57) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c539, c110, c511, c81, c63, c540, c543, c362, c367, c89, c114, c65, c524] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c539 := derived539 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c511 := derived511 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c540 := derived540 a h
  have h6 : Entails.eval a c543 := derived543 a h
  have h7 : Entails.eval a c362 := h 361 (by decide)
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c524 := derived524 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c545 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c511, some c533, some c85, some c111, some c544, some c370, some c379, some c534, some c354, some c539, some c110, some c317, some c340, some c345, some c27, some c71, some c237, some c114, some c32, some c407, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 57) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c497, c511, c533, c85, c111, c544, c370, c379, c534, c354, c539, c110, c317, c340, c345, c27, c71, c237, c114, c32, c407] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c533 := derived533 a h
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c544 := derived544 a h
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c534 := derived534 a h
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c539 := derived539 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c317 := h 316 (by decide)
  have h13 : Entails.eval a c340 := h 339 (by decide)
  have h14 : Entails.eval a c345 := h 344 (by decide)
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c71 := h 70 (by decide)
  have h17 : Entails.eval a c237 := h 236 (by decide)
  have h18 : Entails.eval a c114 := h 113 (by decide)
  have h19 : Entails.eval a c32 := h 31 (by decide)
  have h20 : Entails.eval a c407 := derived407 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c511, some c533, some c85, some c111, some c539, some c110, some c544, some c370, some c379, some c354, some c534, some c545, some c45, some c289, some c50, some c24, some c323, some c237, some c515, some c27, some c362, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 57) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c497, c511, c533, c85, c111, c539, c110, c544, c370, c379, c354, c534, c545, c45, c289, c50, c24, c323, c237, c515, c27, c362] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c533 := derived533 a h
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c539 := derived539 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c544 := derived544 a h
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c534 := derived534 a h
  have h12 : Entails.eval a c545 := derived545 a h
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c289 := h 288 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c24 := h 23 (by decide)
  have h17 : Entails.eval a c323 := h 322 (by decide)
  have h18 : Entails.eval a c237 := h 236 (by decide)
  have h19 : Entails.eval a c515 := derived515 a h
  have h20 : Entails.eval a c27 := h 26 (by decide)
  have h21 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c497, some c370, some c379, some c79, some c61, some c98, some c357, some c112, some c114, some c85, some c72, some c116, some c337, some c73, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 57) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c546, c497, c370, c379, c79, c61, c98, c357, c112, c114, c85, c72, c116, c337, c73] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c357 := h 356 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c337 := h 336 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c362, some c546, some c497, some c89, some c32, some c547, some c63, some c113, some c85, some c357, some c79, some c25, some c230, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 57) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c367, c362, c546, c497, c89, c32, c547, c63, c113, c85, c357, c79, c25, c230] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c362 := h 361 (by decide)
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c547 := derived547 a h
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨3, by decide⟩, false), (⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c548, some c117, some c367, some c362, some c546, some c357, some c79, some c25, some c87, some c230, some c113, some c131, some c13, some c141, some c271, some c270, some c58, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 57) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c548, c117, c367, c362, c546, c357, c79, c25, c87, c230, c113, c131, c13, c141, c271, c270, c58] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c548 := derived548 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c546 := derived546 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c230 := h 229 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c141 := h 140 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c270 := h 269 (by decide)
  have h16 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c497, some c352, some c328, some c320, some c308, some c70, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 57) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c546, c497, c352, c328, c320, c308, c70] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c352 := h 351 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c548, some c362, some c546, some c497, some c63, some c117, some c549, some c85, some c113, some c87, some c550, some c372, some c380, some c98, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 57) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c548, c362, c546, c497, c63, c117, c549, c85, c113, c87, c550, c372, c380, c98] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c548 := derived548 a h
  have h1 : Entails.eval a c362 := h 361 (by decide)
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c549 := derived549 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c550 := derived550 a h
  have h11 : Entails.eval a c372 := h 371 (by decide)
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c362, some c548, some c551, some c370, some c379, some c547, some c79, some c61, some c97, some c98, some c26, some c231, some c117, some c118, some c45, some c72, some c36, some c262, some c199, some c17, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 57) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c546, c362, c548, c551, c370, c379, c547, c79, c61, c97, c98, c26, c231, c117, c118, c45, c72, c36, c262, c199, c17] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c362 := h 361 (by decide)
  have h2 : Entails.eval a c548 := derived548 a h
  have h3 : Entails.eval a c551 := derived551 a h
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c547 := derived547 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c231 := h 230 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c72 := h 71 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c262 := h 261 (by decide)
  have h19 : Entails.eval a c199 := h 198 (by decide)
  have h20 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨45, by decide⟩, true), (⟨43, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c497, some c370, some c379, some c79, some c354, some c357, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 57) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c546, c497, c370, c379, c79, c354, c357] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c552, some c553, some c63, some c546, some c497, some c117, some c88, some c83, some c29, some c357, some c358, some c380, some c241, some c352, some c328, some c131, some c308, some c13, some c43, some c141, some c262, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 57) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c552, c553, c63, c546, c497, c117, c88, c83, c29, c357, c358, c380, c241, c352, c328, c131, c308, c13, c43, c141, c262] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c553 := derived553 a h
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c497 := derived497 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c241 := h 240 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c328 := h 327 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c141 := h 140 (by decide)
  have h20 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c552, some c553, some c63, some c546, some c497, some c357, some c358, some c85, some c354, some c113, some c380, some c89, some c352, some c328, some c313, some c308, some c69, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 57) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c554, c552, c553, c63, c546, c497, c357, c358, c85, c354, c113, c380, c89, c352, c328, c313, c308, c69] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c553 := derived553 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c546 := derived546 a h
  have h5 : Entails.eval a c497 := derived497 a h
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c328 := h 327 (by decide)
  have h15 : Entails.eval a c313 := h 312 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c497, some c552, some c553, some c63, some c554, some c555, some c79, some c25, some c88, some c230, some c112, some c32, some c24, some c87, some c272, some c363, some c141, some c85, some c11, some c12, some c165, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 57) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c546, c497, c552, c553, c63, c554, c555, c79, c25, c88, c230, c112, c32, c24, c87, c272, c363, c141, c85, c11, c12, c165] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c553 := derived553 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c554 := derived554 a h
  have h6 : Entails.eval a c555 := derived555 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c272 := h 271 (by decide)
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c141 := h 140 (by decide)
  have h18 : Entails.eval a c85 := h 84 (by decide)
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c12 := h 11 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨24, by decide⟩, true), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c117, some c87, some c32, some c313, some c322, some c71, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 57) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c112, c117, c87, c32, c313, c322, c71] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c81, some c546, some c497, some c79, some c25, some c372, some c230, some c328, some c350, some c557, some c88, some c393, some c320, some c87, some c394, some c70, some c113, some c339, some c102, some c75, some c115, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c556, c81, c546, c497, c79, c25, c372, c230, c328, c350, c557, c88, c393, c320, c87, c394, c70, c113, c339, c102, c75, c115] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c230 := h 229 (by decide)
  have h8 : Entails.eval a c328 := h 327 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  have h10 : Entails.eval a c557 := derived557 a h
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c393 := derived393 a h
  have h13 : Entails.eval a c320 := h 319 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c394 := derived394 a h
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c113 := h 112 (by decide)
  have h18 : Entails.eval a c339 := h 338 (by decide)
  have h19 : Entails.eval a c102 := h 101 (by decide)
  have h20 : Entails.eval a c75 := h 74 (by decide)
  have h21 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c558, some c556, some c81, some c546, some c497, some c112, some c113, some c67, some c85, some c104, some c310, some c380, some c70, some c328, some c350, some c320, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c558, c556, c81, c546, c497, c112, c113, c67, c85, c104, c310, c380, c70, c328, c350, c320] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c558 := derived558 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c497 := derived497 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c328 := h 327 (by decide)
  have h14 : Entails.eval a c350 := h 349 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨5, by decide⟩, true), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c308, some c320, some c70, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c308, c320, c70] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c308 := h 307 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c372, some c380, some c98, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c546, c372, c380, c98] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c558, some c556, some c546, some c561, some c328, some c350, some c560, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c558, c556, c546, c561, c328, c350, c560] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c558 := derived558 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c561 := derived561 a h
  have h4 : Entails.eval a c328 := h 327 (by decide)
  have h5 : Entails.eval a c350 := h 349 (by decide)
  have h6 : Entails.eval a c560 := derived560 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c81, some c562, some c117, some c559, some c558, some c546, some c80, some c89, some c382, some c372, some c377, some c351, some c329, some c470, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c556, c81, c562, c117, c559, c558, c546, c80, c89, c382, c372, c377, c351, c329, c470] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c562 := derived562 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c559 := derived559 a h
  have h5 : Entails.eval a c558 := derived558 a h
  have h6 : Entails.eval a c546 := derived546 a h
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c382 := derived382 a h
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c351 := h 350 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  have h14 : Entails.eval a c470 := derived470 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c546, some c559, some c563, some c393, some c372, some c97, some c377, some c351, some c329, some c470, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c556, c546, c559, c563, c393, c372, c97, c377, c351, c329, c470] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c559 := derived559 a h
  have h3 : Entails.eval a c563 := derived563 a h
  have h4 : Entails.eval a c393 := derived393 a h
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c470 := derived470 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨45, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c497, some c372, some c380, some c561, some c354, some c112, some c452, some c97, some c377, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c546, c497, c372, c380, c561, c354, c112, c452, c97, c377] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c561 := derived561 a h
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c452 := derived452 a h
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c342, some c313, some c70, some c89, some c117, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c69, c342, c313, c70, c89, c117] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c342 := h 341 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c546, some c497, some c81, some c558, some c564, some c565, some c328, some c350, some c382, some c359, some c308, some c566, some c112, some c113, some c93, some c102, some c115, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c556, c546, c497, c81, c558, c564, c565, c328, c350, c382, c359, c308, c566, c112, c113, c93, c102, c115] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c558 := derived558 a h
  have h5 : Entails.eval a c564 := derived564 a h
  have h6 : Entails.eval a c565 := derived565 a h
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c350 := h 349 (by decide)
  have h9 : Entails.eval a c382 := derived382 a h
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c308 := h 307 (by decide)
  have h12 : Entails.eval a c566 := derived566 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c93 := h 92 (by decide)
  have h16 : Entails.eval a c102 := h 101 (by decide)
  have h17 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨5, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c114, some c72, some c82, some c308, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c112, c114, c72, c82, c308] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c27, some c283, some c231, some c18, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c45, c27, c283, c231, c18] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c231 := h 230 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c370, some c97, some c289, some c283, some c53, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c546, c370, c97, c289, c283, c53] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨35, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c44, some c53, some c18, some c298, some c231, some c258, some c191, some c204, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c51, c44, c53, c18, c298, c231, c258, c191, c204] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c298 := h 297 (by decide)
  have h5 : Entails.eval a c231 := h 230 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c330, some c258, some c339, some c303, some c259, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c330, c258, c339, c303, c259] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c330 := h 329 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c567, some c370, some c379, some c98, some c61, some c79, some c556, some c497, some c568, some c97, some c569, some c117, some c570, some c571, some c572, some c337, some c338, some c259, some c71, some c285, some c342, some c331, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c546, c567, c370, c379, c98, c61, c79, c556, c497, c568, c97, c569, c117, c570, c571, c572, c337, c338, c259, c71, c285, c342, c331] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c567 := derived567 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c497 := derived497 a h
  have h9 : Entails.eval a c568 := derived568 a h
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c569 := derived569 a h
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c570 := derived570 a h
  have h14 : Entails.eval a c571 := derived571 a h
  have h15 : Entails.eval a c572 := derived572 a h
  have h16 : Entails.eval a c337 := h 336 (by decide)
  have h17 : Entails.eval a c338 := h 337 (by decide)
  have h18 : Entails.eval a c259 := h 258 (by decide)
  have h19 : Entails.eval a c71 := h 70 (by decide)
  have h20 : Entails.eval a c285 := h 284 (by decide)
  have h21 : Entails.eval a c342 := h 341 (by decide)
  have h22 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c546, some c567, some c370, some c379, some c98, some c61, some c556, some c97, some c377, some c569, some c117, some c570, some c571, some c284, some c258, some c337, some c338, some c331, some c71, some c342, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c573, c546, c567, c370, c379, c98, c61, c556, c97, c377, c569, c117, c570, c571, c284, c258, c337, c338, c331, c71, c342] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c569 := derived569 a h
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c570 := derived570 a h
  have h13 : Entails.eval a c571 := derived571 a h
  have h14 : Entails.eval a c284 := h 283 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  have h16 : Entails.eval a c337 := h 336 (by decide)
  have h17 : Entails.eval a c338 := h 337 (by decide)
  have h18 : Entails.eval a c331 := h 330 (by decide)
  have h19 : Entails.eval a c71 := h 70 (by decide)
  have h20 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c556, some c567, some c370, some c379, some c79, some c61, some c98, some c574, some c112, some c114, some c72, some c90, some c308, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c546, c556, c567, c370, c379, c79, c61, c98, c574, c112, c114, c72, c90, c308] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c574 := derived574 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨33, by decide⟩, false), (⟨2, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c575, some c335, some c67, some c116, some c113, some c546, some c79, some c307, some c81, some c91, some c379, some c359, some c98, some c90, some c114, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c497, c575, c335, c67, c116, c113, c546, c79, c307, c81, c91, c379, c359, c98, c90, c114] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c335 := h 334 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c546 := derived546 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c98 := h 97 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨2, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c546, some c497, some c335, some c67, some c113, some c116, some c576, some c370, some c372, some c81, some c100, some c330, some c307, some c114, some c337, some c88, some c75, some c317, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c575, c546, c497, c335, c67, c113, c116, c576, c370, c372, c81, c100, c330, c307, c114, c337, c88, c75, c317] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c576 := derived576 a h
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c100 := h 99 (by decide)
  have h12 : Entails.eval a c330 := h 329 (by decide)
  have h13 : Entails.eval a c307 := h 306 (by decide)
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c337 := h 336 (by decide)
  have h16 : Entails.eval a c88 := h 87 (by decide)
  have h17 : Entails.eval a c75 := h 74 (by decide)
  have h18 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨43, by decide⟩, false), (⟨2, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c577, some c43, some c575, some c497, some c70, some c317, some c88, some c29, some c357, some c262, some c208, some c85, some c19, some c113, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c546, c577, c43, c575, c497, c70, c317, c88, c29, c357, c262, c208, c85, c19, c113] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c577 := derived577 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c497 := derived497 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c262 := h 261 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c114, some c100, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c112, c114, c100] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c546, some c497, some c577, some c61, some c43, some c370, some c372, some c282, some c579, some c70, some c578, some c345, some c81, some c50, some c144, some c113, some c13, some c67, some c127, some c209, some c208, some c40, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c575, c546, c497, c577, c61, c43, c370, c372, c282, c579, c70, c578, c345, c81, c50, c144, c113, c13, c67, c127, c209, c208, c40] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c577 := derived577 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c579 := derived579 a h
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c578 := derived578 a h
  have h12 : Entails.eval a c345 := h 344 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c144 := h 143 (by decide)
  have h16 : Entails.eval a c113 := h 112 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c67 := h 66 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  have h20 : Entails.eval a c209 := h 208 (by decide)
  have h21 : Entails.eval a c208 := h 207 (by decide)
  have h22 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived580

end CochromaticTwenty.Certificates.B16_3_1
