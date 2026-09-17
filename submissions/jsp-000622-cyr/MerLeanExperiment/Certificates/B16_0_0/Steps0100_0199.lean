import MerLeanExperiment.Certificates.B16_0_0.Steps0000_0099

/-! Generated from the actual pinned b16_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c494 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c15, some c8, some c120, some c58, some c97, some c160, some c156, some c479, some c53, some c351, some c67, some c178, some c136, some c338, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked494 : lratChecker f494 p494 = .success := by decide +kernel
theorem unsat494 : Unsatisfiable (PosFin 57) f494 := by
  apply lratCheckerSound f494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p494
  · intro a ha; simp [p494] at ha; subst a; trivial
  · exact checked494
theorem derived494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c494 := by
  apply localUnsat_implies_entails f494 [c12, c15, c8, c120, c58, c97, c160, c156, c479, c53, c351, c67, c178, c136, c338] c494 unsat494 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c479 := derived479 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  have h14 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c495 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨21, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c131, some c271, some c129, some c258, some c118, some c120, some c493, some c15, some c12, some c198, some c202, some c122, some c249, some c494, some c389, some c57, some c157, some c156, some c225, some c22, some c280, some c262, some c208, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked495 : lratChecker f495 p495 = .success := by decide +kernel
theorem unsat495 : Unsatisfiable (PosFin 57) f495 := by
  apply lratCheckerSound f495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p495
  · intro a ha; simp [p495] at ha; subst a; trivial
  · exact checked495
theorem derived495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c495 := by
  apply localUnsat_implies_entails f495 [c131, c271, c129, c258, c118, c120, c493, c15, c12, c198, c202, c122, c249, c494, c389, c57, c157, c156, c225, c22, c280, c262, c208] c495 unsat495 (by rfl) a
  have h0 : Entails.eval a c131 := h 130 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c493 := derived493 a h
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c494 := derived494 a h
  have h14 : Entails.eval a c389 := h 388 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c157 := h 156 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c225 := h 224 (by decide)
  have h19 : Entails.eval a c22 := h 21 (by decide)
  have h20 : Entails.eval a c280 := h 279 (by decide)
  have h21 : Entails.eval a c262 := h 261 (by decide)
  have h22 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c496 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c131, some c493, some c258, some c271, some c213, some c495, some c51, some c428, some c112, some c138, some c387, some c101, some c87, some c90, some c370, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked496 : lratChecker f496 p496 = .success := by decide +kernel
theorem unsat496 : Unsatisfiable (PosFin 57) f496 := by
  apply lratCheckerSound f496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p496
  · intro a ha; simp [p496] at ha; subst a; trivial
  · exact checked496
theorem derived496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c496 := by
  apply localUnsat_implies_entails f496 [c131, c493, c258, c271, c213, c495, c51, c428, c112, c138, c387, c101, c87, c90, c370] c496 unsat496 (by rfl) a
  have h0 : Entails.eval a c131 := h 130 (by decide)
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c258 := h 257 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c495 := derived495 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c428 := derived428 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c101 := h 100 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c497 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c120, some c496, some c215, some c312, some c53, some c322, some c60, some c97, some c33, some c5, some c208, some c389, some c262, some c57, some c28, some c158, some c106, some c12, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked497 : lratChecker f497 p497 = .success := by decide +kernel
theorem unsat497 : Unsatisfiable (PosFin 57) f497 := by
  apply lratCheckerSound f497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p497
  · intro a ha; simp [p497] at ha; subst a; trivial
  · exact checked497
theorem derived497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c497 := by
  apply localUnsat_implies_entails f497 [c8, c120, c496, c215, c312, c53, c322, c60, c97, c33, c5, c208, c389, c262, c57, c28, c158, c106, c12] c497 unsat497 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c496 := derived496 a h
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  have h12 : Entails.eval a c389 := h 388 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c158 := h 157 (by decide)
  have h17 : Entails.eval a c106 := h 105 (by decide)
  have h18 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c498 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c120, some c493, some c497, some c55, some c61, some c94, some c6, some c389, some c391, some c58, some c97, some c160, some c112, some c15, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked498 : lratChecker f498 p498 = .success := by decide +kernel
theorem unsat498 : Unsatisfiable (PosFin 57) f498 := by
  apply lratCheckerSound f498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p498
  · intro a ha; simp [p498] at ha; subst a; trivial
  · exact checked498
theorem derived498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c498 := by
  apply localUnsat_implies_entails f498 [c8, c120, c493, c497, c55, c61, c94, c6, c389, c391, c58, c97, c160, c112, c15] c498 unsat498 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c391 := h 390 (by decide)
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c160 := h 159 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c499 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c37, some c258, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked499 : lratChecker f499 p499 = .success := by decide +kernel
theorem unsat499 : Unsatisfiable (PosFin 57) f499 := by
  apply lratCheckerSound f499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p499
  · intro a ha; simp [p499] at ha; subst a; trivial
  · exact checked499
theorem derived499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c499 := by
  apply localUnsat_implies_entails f499 [c101, c37, c258] c499 unsat499 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c500 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨30, by decide⟩, true), (⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c312, some c258, some c215, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked500 : lratChecker f500 p500 = .success := by decide +kernel
theorem unsat500 : Unsatisfiable (PosFin 57) f500 := by
  apply lratCheckerSound f500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p500
  · intro a ha; simp [p500] at ha; subst a; trivial
  · exact checked500
theorem derived500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c500 := by
  apply localUnsat_implies_entails f500 [c312, c258, c215] c500 unsat500 (by rfl) a
  have h0 : Entails.eval a c312 := h 311 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c501 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c120, some c8, some c131, some c498, some c109, some c104, some c499, some c55, some c118, some c500, some c97, some c92, some c308, some c249, some c122, some c28, some c198, some c271, some c15, some c146, some c213, some c51, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked501 : lratChecker f501 p501 = .success := by decide +kernel
theorem unsat501 : Unsatisfiable (PosFin 57) f501 := by
  apply lratCheckerSound f501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p501
  · intro a ha; simp [p501] at ha; subst a; trivial
  · exact checked501
theorem derived501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c501 := by
  apply localUnsat_implies_entails f501 [c493, c120, c8, c131, c498, c109, c104, c499, c55, c118, c500, c97, c92, c308, c249, c122, c28, c198, c271, c15, c146, c213, c51] c501 unsat501 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c498 := derived498 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c499 := derived499 a h
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c500 := derived500 a h
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c308 := h 307 (by decide)
  have h14 : Entails.eval a c249 := h 248 (by decide)
  have h15 : Entails.eval a c122 := h 121 (by decide)
  have h16 : Entails.eval a c28 := h 27 (by decide)
  have h17 : Entails.eval a c198 := h 197 (by decide)
  have h18 : Entails.eval a c271 := h 270 (by decide)
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c146 := h 145 (by decide)
  have h21 : Entails.eval a c213 := h 212 (by decide)
  have h22 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c502 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c58, some c22, some c255, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked502 : lratChecker f502 p502 = .success := by decide +kernel
theorem unsat502 : Unsatisfiable (PosFin 57) f502 := by
  apply lratCheckerSound f502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p502
  · intro a ha; simp [p502] at ha; subst a; trivial
  · exact checked502
theorem derived502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c502 := by
  apply localUnsat_implies_entails f502 [c58, c22, c255] c502 unsat502 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c503 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c351, some c359, some c224, some c349, some c387, some c257, some c428, some c7, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked503 : lratChecker f503 p503 = .success := by decide +kernel
theorem unsat503 : Unsatisfiable (PosFin 57) f503 := by
  apply lratCheckerSound f503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p503
  · intro a ha; simp [p503] at ha; subst a; trivial
  · exact checked503
theorem derived503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c503 := by
  apply localUnsat_implies_entails f503 [c351, c359, c224, c349, c387, c257, c428, c7] c503 unsat503 (by rfl) a
  have h0 : Entails.eval a c351 := h 350 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c224 := h 223 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  have h4 : Entails.eval a c387 := h 386 (by decide)
  have h5 : Entails.eval a c257 := h 256 (by decide)
  have h6 : Entails.eval a c428 := derived428 a h
  have h7 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c504 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c503, some c393, some c259, some c349, some c226, some c359, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked504 : lratChecker f504 p504 = .success := by decide +kernel
theorem unsat504 : Unsatisfiable (PosFin 57) f504 := by
  apply lratCheckerSound f504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p504
  · intro a ha; simp [p504] at ha; subst a; trivial
  · exact checked504
theorem derived504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c504 := by
  apply localUnsat_implies_entails f504 [c493, c503, c393, c259, c349, c226, c359] c504 unsat504 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c503 := derived503 a h
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c349 := h 348 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c505 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c504, some c344, some c219, some c253, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 57) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c493, c504, c344, c219, c253] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c504 := derived504 a h
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c502, some c505, some c355, some c118, some c160, some c15, some c3, some c112, some c106, some c255, some c56, some c20, some c97, some c249, some c259, some c119, some c215, some c311, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 57) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c502, c505, c355, c118, c160, c15, c3, c112, c106, c255, c56, c20, c97, c249, c259, c119, c215, c311] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c502 := derived502 a h
  have h1 : Entails.eval a c505 := derived505 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c255 := h 254 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c97 := h 96 (by decide)
  have h13 : Entails.eval a c249 := h 248 (by decide)
  have h14 : Entails.eval a c259 := h 258 (by decide)
  have h15 : Entails.eval a c119 := h 118 (by decide)
  have h16 : Entails.eval a c215 := h 214 (by decide)
  have h17 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c3, some c146, some c112, some c255, some c54, some c97, some c37, some c259, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 57) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c15, c3, c146, c112, c255, c54, c97, c37, c259] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨30, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c106, some c54, some c65, some c402, some c55, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 57) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c6, c106, c54, c65, c402, c55] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c402 := derived402 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c259, some c508, some c19, some c55, some c402, some c319, some c311, some c141, some c211, some c196, some c267, some c123, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 57) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c6, c259, c508, c19, c55, c402, c319, c311, c141, c211, c196, c267, c123] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c402 := derived402 a h
  have h6 : Entails.eval a c319 := h 318 (by decide)
  have h7 : Entails.eval a c311 := h 310 (by decide)
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c510 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c139, some c150, some c91, some c319, some c372, some c141, some c381, some c196, some c170, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 57) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c55, c139, c150, c91, c319, c372, c141, c381, c196, c170] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c150 := h 149 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c501, some c502, some c505, some c361, some c355, some c506, some c281, some c507, some c160, some c6, some c509, some c510, some c19, some c65, some c106, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 57) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c493, c501, c502, c505, c361, c355, c506, c281, c507, c160, c6, c509, c510, c19, c65, c106] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c501 := derived501 a h
  have h2 : Entails.eval a c502 := derived502 a h
  have h3 : Entails.eval a c505 := derived505 a h
  have h4 : Entails.eval a c361 := h 360 (by decide)
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c506 := derived506 a h
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c507 := derived507 a h
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c509 := derived509 a h
  have h12 : Entails.eval a c510 := derived510 a h
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c65, some c107, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 57) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c19, c65, c107] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨51, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c259, some c211, some c255, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 57) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c259, c211, c255] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c259 := h 258 (by decide)
  have h1 : Entails.eval a c211 := h 210 (by decide)
  have h2 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c514 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨11, by decide⟩, false), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c6, some c511, some c493, some c281, some c361, some c355, some c512, some c55, some c510, some c402, some c393, some c311, some c96, some c513, some c120, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked514 : lratChecker f514 p514 = .success := by decide +kernel
theorem unsat514 : Unsatisfiable (PosFin 57) f514 := by
  apply lratCheckerSound f514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p514
  · intro a ha; simp [p514] at ha; subst a; trivial
  · exact checked514
theorem derived514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c514 := by
  apply localUnsat_implies_entails f514 [c118, c6, c511, c493, c281, c361, c355, c512, c55, c510, c402, c393, c311, c96, c513, c120] c514 unsat514 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c511 := derived511 a h
  have h3 : Entails.eval a c493 := derived493 a h
  have h4 : Entails.eval a c281 := h 280 (by decide)
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c512 := derived512 a h
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c510 := derived510 a h
  have h10 : Entails.eval a c402 := derived402 a h
  have h11 : Entails.eval a c393 := h 392 (by decide)
  have h12 : Entails.eval a c311 := h 310 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c513 := derived513 a h
  have h15 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c515 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, false), (⟨14, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c6, some c493, some c391, some c393, some c344, some c59, some c358, some c353, some c359, some c512, some c226, some c55, some c259, some c120, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked515 : lratChecker f515 p515 = .success := by decide +kernel
theorem unsat515 : Unsatisfiable (PosFin 57) f515 := by
  apply lratCheckerSound f515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p515
  · intro a ha; simp [p515] at ha; subst a; trivial
  · exact checked515
theorem derived515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c515 := by
  apply localUnsat_implies_entails f515 [c118, c6, c493, c391, c393, c344, c59, c358, c353, c359, c512, c226, c55, c259, c120] c515 unsat515 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c391 := h 390 (by decide)
  have h4 : Entails.eval a c393 := h 392 (by decide)
  have h5 : Entails.eval a c344 := h 343 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c512 := derived512 a h
  have h11 : Entails.eval a c226 := h 225 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c516 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨11, by decide⟩, false), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c6, some c511, some c493, some c514, some c515, some c510, some c19, some c107, some c54, some c10, some c119, some c152, some c56, some c20, some c249, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked516 : lratChecker f516 p516 = .success := by decide +kernel
theorem unsat516 : Unsatisfiable (PosFin 57) f516 := by
  apply lratCheckerSound f516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p516
  · intro a ha; simp [p516] at ha; subst a; trivial
  · exact checked516
theorem derived516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c516 := by
  apply localUnsat_implies_entails f516 [c118, c6, c511, c493, c514, c515, c510, c19, c107, c54, c10, c119, c152, c56, c20, c249] c516 unsat516 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c511 := derived511 a h
  have h3 : Entails.eval a c493 := derived493 a h
  have h4 : Entails.eval a c514 := derived514 a h
  have h5 : Entails.eval a c515 := derived515 a h
  have h6 : Entails.eval a c510 := derived510 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c517 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c8, some c55, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked517 : lratChecker f517 p517 = .success := by decide +kernel
theorem unsat517 : Unsatisfiable (PosFin 57) f517 := by
  apply lratCheckerSound f517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p517
  · intro a ha; simp [p517] at ha; subst a; trivial
  · exact checked517
theorem derived517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c517 := by
  apply localUnsat_implies_entails f517 [c120, c8, c55] c517 unsat517 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c518 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c118, some c517, some c502, some c516, some c15, some c54, some c150, some c146, some c323, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked518 : lratChecker f518 p518 = .success := by decide +kernel
theorem unsat518 : Unsatisfiable (PosFin 57) f518 := by
  apply lratCheckerSound f518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p518
  · intro a ha; simp [p518] at ha; subst a; trivial
  · exact checked518
theorem derived518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c518 := by
  apply localUnsat_implies_entails f518 [c6, c118, c517, c502, c516, c15, c54, c150, c146, c323] c518 unsat518 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c517 := derived517 a h
  have h3 : Entails.eval a c502 := derived502 a h
  have h4 : Entails.eval a c516 := derived516 a h
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c150 := h 149 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c519 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨30, by decide⟩, false), (⟨14, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c323, some c19, some c107, some c54, some c10, some c146, some c198, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 57) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c55, c323, c19, c107, c54, c10, c146, c198] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨30, by decide⟩, false), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c519, some c150, some c54, some c319, some c15, some c141, some c198, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 57) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c519, c150, c54, c319, c15, c141, c198] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c519 := derived519 a h
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨35, by decide⟩, false), (⟨14, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c520, some c61, some c99, some c35, some c281, some c355, some c160, some c387, some c393, some c257, some c15, some c3, some c146, some c342, some c101, some c131, some c267, some c287, some c52, some c124, some c220, some c145, some c158, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 57) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c520, c61, c99, c35, c281, c355, c160, c387, c393, c257, c15, c3, c146, c342, c101, c131, c267, c287, c52, c124, c220, c145, c158] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c520 := derived520 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c281 := h 280 (by decide)
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c387 := h 386 (by decide)
  have h8 : Entails.eval a c393 := h 392 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c146 := h 145 (by decide)
  have h13 : Entails.eval a c342 := h 341 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c267 := h 266 (by decide)
  have h17 : Entails.eval a c287 := h 286 (by decide)
  have h18 : Entails.eval a c52 := h 51 (by decide)
  have h19 : Entails.eval a c124 := h 123 (by decide)
  have h20 : Entails.eval a c220 := h 219 (by decide)
  have h21 : Entails.eval a c145 := h 144 (by decide)
  have h22 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c522 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨35, by decide⟩, false), (⟨14, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c99, some c35, some c355, some c160, some c387, some c393, some c257, some c15, some c3, some c13, some c56, some c101, some c119, some c131, some c267, some c43, some c52, some c124, some c202, some c197, some c140, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 57) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c61, c99, c35, c355, c160, c387, c393, c257, c15, c3, c13, c56, c101, c119, c131, c267, c43, c52, c124, c202, c197, c140] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c387 := h 386 (by decide)
  have h6 : Entails.eval a c393 := h 392 (by decide)
  have h7 : Entails.eval a c257 := h 256 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c131 := h 130 (by decide)
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c43 := h 42 (by decide)
  have h17 : Entails.eval a c52 := h 51 (by decide)
  have h18 : Entails.eval a c124 := h 123 (by decide)
  have h19 : Entails.eval a c202 := h 201 (by decide)
  have h20 : Entails.eval a c197 := h 196 (by decide)
  have h21 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c523 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨19, by decide⟩, false), (⟨35, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c255, some c96, some c387, some c56, some c353, some c355, some c219, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 57) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c267, c255, c96, c387, c56, c353, c355, c219] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c255 := h 254 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c353 := h 352 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c524 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨12, by decide⟩, false), (⟨19, by decide⟩, false), (⟨35, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c353, some c219, some c344, some c262, some c389, some c122, some c96, some c153, some c257, some c23, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 57) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c493, c353, c219, c344, c262, c389, c122, c96, c153, c257, c23] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c389 := h 388 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c525 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c20, some c249, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 57) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c56, c20, c249] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c511, some c518, some c522, some c15, some c3, some c13, some c107, some c523, some c131, some c525, some c355, some c524, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 57) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c493, c511, c518, c522, c15, c3, c13, c107, c523, c131, c525, c355, c524] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c518 := derived518 a h
  have h3 : Entails.eval a c522 := derived522 a h
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c523 := derived523 a h
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c525 := derived525 a h
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c524 := derived524 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c518, some c526, some c198, some c160, some c493, some c511, some c521, some c120, some c131, some c122, some c500, some c265, some c351, some c23, some c32, some c359, some c262, some c219, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 57) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c518, c526, c198, c160, c493, c511, c521, c120, c131, c122, c500, c265, c351, c23, c32, c359, c262, c219] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c526 := derived526 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c493 := derived493 a h
  have h5 : Entails.eval a c511 := derived511 a h
  have h6 : Entails.eval a c521 := derived521 a h
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c500 := derived500 a h
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c351 := h 350 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c262 := h 261 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c528 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c527, some c518, some c526, some c160, some c493, some c511, some c522, some c267, some c255, some c523, some c219, some c96, some c107, some c156, some c393, some c19, some c2, some c97, some c110, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 57) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c527, c518, c526, c160, c493, c511, c522, c267, c255, c523, c219, c96, c107, c156, c393, c19, c2, c97, c110] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c527 := derived527 a h
  have h1 : Entails.eval a c518 := derived518 a h
  have h2 : Entails.eval a c526 := derived526 a h
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c493 := derived493 a h
  have h5 : Entails.eval a c511 := derived511 a h
  have h6 : Entails.eval a c522 := derived522 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c523 := derived523 a h
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c107 := h 106 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c393 := h 392 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c97 := h 96 (by decide)
  have h18 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨38, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c219, some c358, some c353, some c156, some c512, some c2, some c124, some c110, some c271, some c33, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 57) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c219, c358, c353, c156, c512, c2, c124, c110, c271, c33] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c219 := h 218 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c512 := derived512 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c518, some c511, some c493, some c522, some c526, some c160, some c198, some c527, some c528, some c32, some c529, some c253, some c269, some c263, some c344, some c33, some c1, some c358, some c353, some c156, some c107, some c512, some c12, some c110, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 57) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c518, c511, c493, c522, c526, c160, c198, c527, c528, c32, c529, c253, c269, c263, c344, c33, c1, c358, c353, c156, c107, c512, c12, c110] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c522 := derived522 a h
  have h4 : Entails.eval a c526 := derived526 a h
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c527 := derived527 a h
  have h8 : Entails.eval a c528 := derived528 a h
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c529 := derived529 a h
  have h11 : Entails.eval a c253 := h 252 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c1 := h 0 (by decide)
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c353 := h 352 (by decide)
  have h19 : Entails.eval a c156 := h 155 (by decide)
  have h20 : Entails.eval a c107 := h 106 (by decide)
  have h21 : Entails.eval a c512 := derived512 a h
  have h22 : Entails.eval a c12 := h 11 (by decide)
  have h23 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨23, by decide⟩, false), (⟨50, by decide⟩, true), (⟨24, by decide⟩, true), (⟨36, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c493, some c61, some c344, some c517, some c359, some c500, some c351, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 57) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c120, c493, c61, c344, c517, c359, c500, c351] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c517 := derived517 a h
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c500 := derived500 a h
  have h7 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c530, some c502, some c131, some c8, some c120, some c58, some c389, some c511, some c68, some c493, some c354, some c359, some c525, some c69, some c53, some c110, some c94, some c517, some c107, some c215, some c495, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 57) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c530, c502, c131, c8, c120, c58, c389, c511, c68, c493, c354, c359, c525, c69, c53, c110, c94, c517, c107, c215, c495] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c502 := derived502 a h
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c511 := derived511 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c493 := derived493 a h
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c359 := h 358 (by decide)
  have h12 : Entails.eval a c525 := derived525 a h
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c94 := h 93 (by decide)
  have h17 : Entails.eval a c517 := derived517 a h
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c215 := h 214 (by decide)
  have h20 : Entails.eval a c495 := derived495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c511, some c518, some c530, some c58, some c22, some c68, some c502, some c389, some c120, some c8, some c131, some c531, some c532, some c57, some c110, some c47, some c69, some c499, some c362, some c517, some c70, some c208, some c107, some c262, some c525, some c122, some c154, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 57) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c493, c511, c518, c530, c58, c22, c68, c502, c389, c120, c8, c131, c531, c532, c57, c110, c47, c69, c499, c362, c517, c70, c208, c107, c262, c525, c122, c154] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c511 := derived511 a h
  have h2 : Entails.eval a c518 := derived518 a h
  have h3 : Entails.eval a c530 := derived530 a h
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c502 := derived502 a h
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c531 := derived531 a h
  have h13 : Entails.eval a c532 := derived532 a h
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c47 := h 46 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c499 := derived499 a h
  have h19 : Entails.eval a c362 := h 361 (by decide)
  have h20 : Entails.eval a c517 := derived517 a h
  have h21 : Entails.eval a c70 := h 69 (by decide)
  have h22 : Entails.eval a c208 := h 207 (by decide)
  have h23 : Entails.eval a c107 := h 106 (by decide)
  have h24 : Entails.eval a c262 := h 261 (by decide)
  have h25 : Entails.eval a c525 := derived525 a h
  have h26 : Entails.eval a c122 := h 121 (by decide)
  have h27 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c111, some c10, some c19, some c8, some c118, some c48, some c54, some c150, some c146, some c196, some c123, some c143, some c267, some c269, some c322, some c211, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 57) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c105, c111, c10, c19, c8, c118, c48, c54, c150, c146, c196, c123, c143, c267, c269, c322, c211] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c150 := h 149 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c267 := h 266 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c322 := h 321 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c525, some c56, some c20, some c119, some c127, some c387, some c246, some c262, some c54, some c346, some c124, some c220, some c208, some c197, some c284, some c44, some c144, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 57) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c105, c525, c56, c20, c119, c127, c387, c246, c262, c54, c346, c124, c220, c208, c197, c284, c44, c144] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c525 := derived525 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c387 := h 386 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  have h8 : Entails.eval a c262 := h 261 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c220 := h 219 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c197 := h 196 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c44 := h 43 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c533, some c493, some c105, some c111, some c8, some c19, some c10, some c475, some c534, some c198, some c535, some c154, some c344, some c219, some c253, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 57) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c533, c493, c105, c111, c8, c19, c10, c475, c534, c198, c535, c154, c344, c219, c253] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c533 := derived533 a h
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c475 := derived475 a h
  have h8 : Entails.eval a c534 := derived534 a h
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c535 := derived535 a h
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c344 := h 343 (by decide)
  have h13 : Entails.eval a c219 := h 218 (by decide)
  have h14 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c108, some c103, some c19, some c10, some c154, some c198, some c525, some c56, some c20, some c127, some c387, some c246, some c262, some c346, some c99, some c220, some c112, some c362, some c64, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 57) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c61, c108, c103, c19, c10, c154, c198, c525, c56, c20, c127, c387, c246, c262, c346, c99, c220, c112, c362, c64] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c525 := derived525 a h
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c346 := h 345 (by decide)
  have h15 : Entails.eval a c99 := h 98 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c112 := h 111 (by decide)
  have h18 : Entails.eval a c362 := h 361 (by decide)
  have h19 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c35, some c257, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 57) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c99, c35, c257] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c533, some c493, some c536, some c61, some c6, some c537, some c475, some c57, some c120, some c131, some c389, some c391, some c499, some c347, some c538, some c112, some c492, some c67, some c288, some c362, some c225, some c265, some c357, some c218, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 57) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c533, c493, c536, c61, c6, c537, c475, c57, c120, c131, c389, c391, c499, c347, c538, c112, c492, c67, c288, c362, c225, c265, c357, c218] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c533 := derived533 a h
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c536 := derived536 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c537 := derived537 a h
  have h6 : Entails.eval a c475 := derived475 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c391 := h 390 (by decide)
  have h12 : Entails.eval a c499 := derived499 a h
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c538 := derived538 a h
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c492 := derived492 a h
  have h17 : Entails.eval a c67 := h 66 (by decide)
  have h18 : Entails.eval a c288 := h 287 (by decide)
  have h19 : Entails.eval a c362 := h 361 (by decide)
  have h20 : Entails.eval a c225 := h 224 (by decide)
  have h21 : Entails.eval a c265 := h 264 (by decide)
  have h22 : Entails.eval a c357 := h 356 (by decide)
  have h23 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨35, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c493, some c61, some c539, some c533, some c120, some c8, some c131, some c108, some c499, some c538, some c94, some c53, some c112, some c389, some c391, some c492, some c12, some c347, some c288, some c158, some c359, some c117, some c225, some c271, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 57) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c6, c493, c61, c539, c533, c120, c8, c131, c108, c499, c538, c94, c53, c112, c389, c391, c492, c12, c347, c288, c158, c359, c117, c225, c271] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c533 := derived533 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c499 := derived499 a h
  have h10 : Entails.eval a c538 := derived538 a h
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c389 := h 388 (by decide)
  have h15 : Entails.eval a c391 := h 390 (by decide)
  have h16 : Entails.eval a c492 := derived492 a h
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c347 := h 346 (by decide)
  have h19 : Entails.eval a c288 := h 287 (by decide)
  have h20 : Entails.eval a c158 := h 157 (by decide)
  have h21 : Entails.eval a c359 := h 358 (by decide)
  have h22 : Entails.eval a c117 := h 116 (by decide)
  have h23 : Entails.eval a c225 := h 224 (by decide)
  have h24 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c30, some c253, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 57) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c94, c30, c253] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨35, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c539, some c533, some c493, some c61, some c6, some c540, some c541, some c108, some c103, some c10, some c154, some c65, some c56, some c360, some c387, some c64, some c99, some c109, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 57) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c539, c533, c493, c61, c6, c540, c541, c108, c103, c10, c154, c65, c56, c360, c387, c64, c99, c109] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c539 := derived539 a h
  have h1 : Entails.eval a c533 := derived533 a h
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c540 := derived540 a h
  have h6 : Entails.eval a c541 := derived541 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c360 := h 359 (by decide)
  have h14 : Entails.eval a c387 := h 386 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c99 := h 98 (by decide)
  have h17 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨35, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c533, some c542, some c105, some c111, some c10, some c19, some c8, some c534, some c539, some c505, some c112, some c154, some c64, some c512, some c360, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 57) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c533, c542, c105, c111, c10, c19, c8, c534, c539, c505, c112, c154, c64, c512, c360] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c533 := derived533 a h
  have h1 : Entails.eval a c542 := derived542 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c534 := derived534 a h
  have h8 : Entails.eval a c539 := derived539 a h
  have h9 : Entails.eval a c505 := derived505 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c512 := derived512 a h
  have h14 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c127, some c124, some c267, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 57) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c127, c124, c267] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c127 := h 126 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c545 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c533, some c539, some c542, some c105, some c111, some c534, some c8, some c10, some c198, some c543, some c17, some c197, some c544, some c525, some c354, some c59, some c23, some c257, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 57) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c533, c539, c542, c105, c111, c534, c8, c10, c198, c543, c17, c197, c544, c525, c354, c59, c23, c257] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c533 := derived533 a h
  have h1 : Entails.eval a c539 := derived539 a h
  have h2 : Entails.eval a c542 := derived542 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c534 := derived534 a h
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c543 := derived543 a h
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c544 := derived544 a h
  have h13 : Entails.eval a c525 := derived525 a h
  have h14 : Entails.eval a c354 := h 353 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c23 := h 22 (by decide)
  have h17 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨24, by decide⟩, false), (⟨35, by decide⟩, false), (⟨22, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c355, some c344, some c219, some c253, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 57) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c353, c355, c344, c219, c253] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c545, some c546, some c533, some c475, some c103, some c10, some c65, some c525, some c198, some c361, some c127, some c219, some c267, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 57) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c493, c545, c546, c533, c475, c103, c10, c65, c525, c198, c361, c127, c219, c267] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c533 := derived533 a h
  have h4 : Entails.eval a c475 := derived475 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c525 := derived525 a h
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨8, by decide⟩, true), (⟨33, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c512, some c65, some c541, some c103, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 57) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c512, c65, c541, c103] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c512 := derived512 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c541 := derived541 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c545, some c546, some c533, some c548, some c358, some c361, some c547, some c61, some c534, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 57) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c493, c545, c546, c533, c548, c358, c361, c547, c61, c534] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c545 := derived545 a h
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c533 := derived533 a h
  have h4 : Entails.eval a c548 := derived548 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c361 := h 360 (by decide)
  have h7 : Entails.eval a c547 := derived547 a h
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c534 := derived534 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c533, some c493, some c549, some c111, some c108, some c541, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 57) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c533, c493, c549, c111, c108, c541] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c533 := derived533 a h
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c549 := derived549 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c541 := derived541 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c533, some c545, some c550, some c120, some c8, some c49, some c111, some c108, some c61, some c6, some c30, some c361, some c355, some c160, some c218, some c115, some c262, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 57) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c493, c533, c545, c550, c120, c8, c49, c111, c108, c61, c6, c30, c361, c355, c160, c218, c115, c262] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c533 := derived533 a h
  have h2 : Entails.eval a c545 := derived545 a h
  have h3 : Entails.eval a c550 := derived550 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c361 := h 360 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c218 := h 217 (by decide)
  have h16 : Entails.eval a c115 := h 114 (by decide)
  have h17 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, true), (⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c134, some c237, some c233, some c291, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 57) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c115, c134, c237, c233, c291] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c237 := h 236 (by decide)
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c196, some c11, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 57) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c198, c196, c11] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨24, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c131, some c266, some c122, some c8, some c120, some c49, some c111, some c108, some c94, some c391, some c101, some c553, some c115, some c134, some c237, some c85, some c372, some c178, some c383, some c88, some c370, some c176, some c12, some c185, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 57) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c131, c266, c122, c8, c120, c49, c111, c108, c94, c391, c101, c553, c115, c134, c237, c85, c372, c178, c383, c88, c370, c176, c12, c185] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c131 := h 130 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c391 := h 390 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c553 := derived553 a h
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c237 := h 236 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  have h16 : Entails.eval a c372 := h 371 (by decide)
  have h17 : Entails.eval a c178 := h 177 (by decide)
  have h18 : Entails.eval a c383 := h 382 (by decide)
  have h19 : Entails.eval a c88 := h 87 (by decide)
  have h20 : Entails.eval a c370 := h 369 (by decide)
  have h21 : Entails.eval a c176 := h 175 (by decide)
  have h22 : Entails.eval a c12 := h 11 (by decide)
  have h23 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c94, some c389, some c58, some c361, some c355, some c218, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 57) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c61, c94, c389, c58, c361, c355, c218] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c94 := h 93 (by decide)
  have h2 : Entails.eval a c389 := h 388 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c361 := h 360 (by decide)
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨27, by decide⟩, true), (⟨33, by decide⟩, false), (⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c389, some c307, some c58, some c552, some c353, some c21, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 57) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c389, c307, c58, c552, c353, c21] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c389 := h 388 (by decide)
  have h1 : Entails.eval a c307 := h 306 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c552 := derived552 a h
  have h4 : Entails.eval a c353 := h 352 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨33, by decide⟩, false), (⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c134, some c237, some c137, some c154, some c556, some c344, some c365, some c151, some c233, some c2, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 57) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c3, c134, c237, c137, c154, c556, c344, c365, c151, c233, c2] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c237 := h 236 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c556 := derived556 a h
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c233 := h 232 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c266, some c493, some c15, some c107, some c525, some c557, some c308, some c58, some c353, some c273, some c57, some c391, some c97, some c53, some c112, some c206, some c13, some c271, some c153, some c23, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c55, c266, c493, c15, c107, c525, c557, c308, c58, c353, c273, c57, c391, c97, c53, c112, c206, c13, c271, c153, c23] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c525 := derived525 a h
  have h6 : Entails.eval a c557 := derived557 a h
  have h7 : Entails.eval a c308 := h 307 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c273 := h 272 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c391 := h 390 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c271 := h 270 (by decide)
  have h19 : Entails.eval a c153 := h 152 (by decide)
  have h20 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c551, some c554, some c131, some c266, some c122, some c8, some c120, some c555, some c55, some c558, some c198, some c196, some c137, some c12, some c90, some c91, some c178, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c493, c551, c554, c131, c266, c122, c8, c120, c555, c55, c558, c198, c196, c137, c12, c90, c91, c178] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c551 := derived551 a h
  have h2 : Entails.eval a c554 := derived554 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c555 := derived555 a h
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c558 := derived558 a h
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c91 := h 90 (by decide)
  have h17 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨30, by decide⟩, true), (⟨26, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c196, some c142, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c198, c196, c142] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c8, some c559, some c47, some c110, some c493, some c551, some c554, some c131, some c266, some c122, some c55, some c560, some c15, some c107, some c28, some c258, some c271, some c97, some c129, some c308, some c197, some c552, some c114, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c120, c8, c559, c47, c110, c493, c551, c554, c131, c266, c122, c55, c560, c15, c107, c28, c258, c271, c97, c129, c308, c197, c552, c114] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c559 := derived559 a h
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c493 := derived493 a h
  have h6 : Entails.eval a c551 := derived551 a h
  have h7 : Entails.eval a c554 := derived554 a h
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c560 := derived560 a h
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c258 := h 257 (by decide)
  have h17 : Entails.eval a c271 := h 270 (by decide)
  have h18 : Entails.eval a c97 := h 96 (by decide)
  have h19 : Entails.eval a c129 := h 128 (by decide)
  have h20 : Entails.eval a c308 := h 307 (by decide)
  have h21 : Entails.eval a c197 := h 196 (by decide)
  have h22 : Entails.eval a c552 := derived552 a h
  have h23 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c551, some c493, some c8, some c131, some c266, some c559, some c110, some c561, some c101, some c393, some c258, some c99, some c28, some c104, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c551, c493, c8, c131, c266, c559, c110, c561, c101, c393, c258, c99, c28, c104] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c551 := derived551 a h
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c559 := derived559 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c561 := derived561 a h
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c393 := h 392 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c391, some c259, some c94, some c33, some c108, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c101, c391, c259, c94, c33, c108] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c259 := h 258 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨21, by decide⟩, true), (⟨1, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c126, some c49, some c40, some c202, some c150, some c148, some c206, some c324, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c115, c126, c49, c40, c202, c150, c148, c206, c324] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c126 := h 125 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c150 := h 149 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨34, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c156, some c121, some c222, some c158, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c196, c156, c121, c222, c158] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c222 := h 221 (by decide)
  have h4 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨1, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨34, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c565, some c3, some c564, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c565, c3, c564] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c565 := derived565 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c564 := derived564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨20, by decide⟩, true), (⟨1, by decide⟩, false), (⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c125, some c49, some c40, some c197, some c141, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c115, c125, c49, c40, c197, c141] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨34, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c221, some c359, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c347, c221, c359] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨23, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨34, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c566, some c271, some c568, some c156, some c3, some c567, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c566, c271, c568, c156, c3, c567] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c566 := derived566 a h
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c568 := derived568 a h
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c567 := derived567 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨34, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c569, some c525, some c1, some c151, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c569, c525, c1, c151] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c569 := derived569 a h
  have h1 : Entails.eval a c525 := derived525 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨55, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨34, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c570, some c119, some c7, some c127, some c196, some c1, some c113, some c43, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c570, c119, c7, c127, c196, c1, c113, c43] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c570 := derived570 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c61, some c551, some c562, some c270, some c563, some c110, some c475, some c94, some c389, some c391, some c253, some c2, some c571, some c266, some c119, some c7, some c127, some c52, some c112, some c196, some c156, some c99, some c347, some c223, some c387, some c158, some c357, some c56, some c140, some c43, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c493, c61, c551, c562, c270, c563, c110, c475, c94, c389, c391, c253, c2, c571, c266, c119, c7, c127, c52, c112, c196, c156, c99, c347, c223, c387, c158, c357, c56, c140, c43] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c551 := derived551 a h
  have h3 : Entails.eval a c562 := derived562 a h
  have h4 : Entails.eval a c270 := h 269 (by decide)
  have h5 : Entails.eval a c563 := derived563 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c475 := derived475 a h
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c391 := h 390 (by decide)
  have h11 : Entails.eval a c253 := h 252 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c571 := derived571 a h
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c119 := h 118 (by decide)
  have h16 : Entails.eval a c7 := h 6 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  have h18 : Entails.eval a c52 := h 51 (by decide)
  have h19 : Entails.eval a c112 := h 111 (by decide)
  have h20 : Entails.eval a c196 := h 195 (by decide)
  have h21 : Entails.eval a c156 := h 155 (by decide)
  have h22 : Entails.eval a c99 := h 98 (by decide)
  have h23 : Entails.eval a c347 := h 346 (by decide)
  have h24 : Entails.eval a c223 := h 222 (by decide)
  have h25 : Entails.eval a c387 := h 386 (by decide)
  have h26 : Entails.eval a c158 := h 157 (by decide)
  have h27 : Entails.eval a c357 := h 356 (by decide)
  have h28 : Entails.eval a c56 := h 55 (by decide)
  have h29 : Entails.eval a c140 := h 139 (by decide)
  have h30 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c391, some c253, some c101, some c2, some c112, some c17, some c99, some c185, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c94, c391, c253, c101, c2, c112, c17, c99, c185] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c112, some c17, some c99, some c197, some c202, some c10, some c103, some c32, some c257, some c119, some c52, some c43, some c140, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c19, c112, c17, c99, c197, c202, c10, c103, c32, c257, c119, c52, c43, c140] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c493, some c562, some c572, some c19, some c573, some c551, some c270, some c574, some c101, some c393, some c259, some c99, some c104, some c10, some c28, some c196, some c266, some c127, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c493, c562, c572, c19, c573, c551, c270, c574, c101, c393, c259, c99, c104, c10, c28, c196, c266, c127] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c493 := derived493 a h
  have h1 : Entails.eval a c562 := derived562 a h
  have h2 : Entails.eval a c572 := derived572 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c573 := derived573 a h
  have h5 : Entails.eval a c551 := derived551 a h
  have h6 : Entails.eval a c270 := h 269 (by decide)
  have h7 : Entails.eval a c574 := derived574 a h
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c393 := h 392 (by decide)
  have h10 : Entails.eval a c259 := h 258 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c10 := h 9 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c196 := h 195 (by decide)
  have h16 : Entails.eval a c266 := h 265 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c493, some c562, some c572, some c19, some c573, some c61, some c551, some c270, some c393, some c259, some c99, some c112, some c104, some c24, some c33, some c5, some c10, some c28, some c266, some c119, some c127, some c124, some c311, some c51, some c263, some c211, some c116, some c44, some c162, some c560, some c221, some c281, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c575, c493, c562, c572, c19, c573, c61, c551, c270, c393, c259, c99, c112, c104, c24, c33, c5, c10, c28, c266, c119, c127, c124, c311, c51, c263, c211, c116, c44, c162, c560, c221, c281] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c562 := derived562 a h
  have h3 : Entails.eval a c572 := derived572 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c573 := derived573 a h
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c551 := derived551 a h
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c393 := h 392 (by decide)
  have h10 : Entails.eval a c259 := h 258 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c10 := h 9 (by decide)
  have h18 : Entails.eval a c28 := h 27 (by decide)
  have h19 : Entails.eval a c266 := h 265 (by decide)
  have h20 : Entails.eval a c119 := h 118 (by decide)
  have h21 : Entails.eval a c127 := h 126 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c311 := h 310 (by decide)
  have h24 : Entails.eval a c51 := h 50 (by decide)
  have h25 : Entails.eval a c263 := h 262 (by decide)
  have h26 : Entails.eval a c211 := h 210 (by decide)
  have h27 : Entails.eval a c116 := h 115 (by decide)
  have h28 : Entails.eval a c44 := h 43 (by decide)
  have h29 : Entails.eval a c162 := h 161 (by decide)
  have h30 : Entails.eval a c560 := derived560 a h
  have h31 : Entails.eval a c221 := h 220 (by decide)
  have h32 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨23, by decide⟩, true), (⟨38, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c355, some c357, some c223, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c355, c357, c223] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c355 := h 354 (by decide)
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨49, by decide⟩, true), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨7, by decide⟩, false), (⟨38, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c119, some c124, some c52, some c269, some c117, some c577, some c342, some c56, some c435, some c43, some c263, some c206, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c112, c119, c124, c52, c269, c117, c577, c342, c56, c435, c43, c263, c206] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c577 := derived577 a h
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c435 := derived435 a h
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c551, some c562, some c270, some c493, some c61, some c572, some c19, some c573, some c575, some c576, some c101, some c112, some c17, some c99, some c387, some c578, some c257, some c23, some c32, some c103, some c10, some c56, some c153, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c551, c562, c270, c493, c61, c572, c19, c573, c575, c576, c101, c112, c17, c99, c387, c578, c257, c23, c32, c103, c10, c56, c153] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c551 := derived551 a h
  have h1 : Entails.eval a c562 := derived562 a h
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c493 := derived493 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c572 := derived572 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c573 := derived573 a h
  have h8 : Entails.eval a c575 := derived575 a h
  have h9 : Entails.eval a c576 := derived576 a h
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c387 := h 386 (by decide)
  have h15 : Entails.eval a c578 := derived578 a h
  have h16 : Entails.eval a c257 := h 256 (by decide)
  have h17 : Entails.eval a c23 := h 22 (by decide)
  have h18 : Entails.eval a c32 := h 31 (by decide)
  have h19 : Entails.eval a c103 := h 102 (by decide)
  have h20 : Entails.eval a c10 := h 9 (by decide)
  have h21 : Entails.eval a c56 := h 55 (by decide)
  have h22 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c153, some c221, some c59, some c257, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c17, c153, c221, c59, c257] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c153 := h 152 (by decide)
  have h2 : Entails.eval a c221 := h 220 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c551, some c266, some c20, some c1, some c579, some c562, some c270, some c22, some c111, some c19, some c580, some c112, some c28, some c271, some c221, some c153, some c354, some c116, some c125, some c475, some c51, some c45, some c196, some c143, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c551, c266, c20, c1, c579, c562, c270, c22, c111, c19, c580, c112, c28, c271, c221, c153, c354, c116, c125, c475, c51, c45, c196, c143] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c551 := derived551 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c579 := derived579 a h
  have h5 : Entails.eval a c562 := derived562 a h
  have h6 : Entails.eval a c270 := h 269 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c580 := derived580 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c221 := h 220 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c116 := h 115 (by decide)
  have h18 : Entails.eval a c125 := h 124 (by decide)
  have h19 : Entails.eval a c475 := derived475 a h
  have h20 : Entails.eval a c51 := h 50 (by decide)
  have h21 : Entails.eval a c45 := h 44 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  have h23 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c551, some c266, some c579, some c562, some c270, some c493, some c1, some c20, some c581, some c355, some c353, some c152, some c475, some c344, some c3, some c115, some c391, some c253, some c111, some c44, some c19, some c114, some c197, some c179, some c17, some c428, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c551, c266, c579, c562, c270, c493, c1, c20, c581, c355, c353, c152, c475, c344, c3, c115, c391, c253, c111, c44, c19, c114, c197, c179, c17, c428] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c551 := derived551 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c579 := derived579 a h
  have h3 : Entails.eval a c562 := derived562 a h
  have h4 : Entails.eval a c270 := h 269 (by decide)
  have h5 : Entails.eval a c493 := derived493 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c581 := derived581 a h
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c475 := derived475 a h
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c391 := h 390 (by decide)
  have h17 : Entails.eval a c253 := h 252 (by decide)
  have h18 : Entails.eval a c111 := h 110 (by decide)
  have h19 : Entails.eval a c44 := h 43 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c114 := h 113 (by decide)
  have h22 : Entails.eval a c197 := h 196 (by decide)
  have h23 : Entails.eval a c179 := h 178 (by decide)
  have h24 : Entails.eval a c17 := h 16 (by decide)
  have h25 : Entails.eval a c428 := derived428 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c110, some c32, some c33, some c271, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c104, c110, c32, c33, c271] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c579, some c551, some c562, some c270, some c582, some c105, some c107, some c502, some c3, some c19, some c583, some c475, some c12, some c156, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c579, c551, c562, c270, c582, c105, c107, c502, c3, c19, c583, c475, c12, c156] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c579 := derived579 a h
  have h1 : Entails.eval a c551 := derived551 a h
  have h2 : Entails.eval a c562 := derived562 a h
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c582 := derived582 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c502 := derived502 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c583 := derived583 a h
  have h11 : Entails.eval a c475 := derived475 a h
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨11, by decide⟩, false), (⟨7, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c502, some c475, some c156, some c353, some c2, some c20, some c269, some c263, some c33, some c32, some c112, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c502, c475, c156, c353, c2, c20, c269, c263, c33, c32, c112] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c502 := derived502 a h
  have h1 : Entails.eval a c475 := derived475 a h
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨11, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c270, some c493, some c111, some c585, some c110, some c33, some c259, some c97, some c92, some c389, some c180, some c387, some c304, some c420, some c132, some c365, some c370, some c375, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c107, c270, c493, c111, c585, c110, c33, c259, c97, c92, c389, c180, c387, c304, c420, c132, c365, c370, c375] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c493 := derived493 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c585 := derived585 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c259 := h 258 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c387 := h 386 (by decide)
  have h13 : Entails.eval a c304 := h 303 (by decide)
  have h14 : Entails.eval a c420 := derived420 a h
  have h15 : Entails.eval a c132 := h 131 (by decide)
  have h16 : Entails.eval a c365 := h 364 (by decide)
  have h17 : Entails.eval a c370 := h 369 (by decide)
  have h18 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c551, some c562, some c270, some c579, some c584, some c119, some c7, some c127, some c54, some c107, some c586, some c10, some c198, some c137, some c90, some c244, some c178, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c551, c562, c270, c579, c584, c119, c7, c127, c54, c107, c586, c10, c198, c137, c90, c244, c178] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c551 := derived551 a h
  have h1 : Entails.eval a c562 := derived562 a h
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c579 := derived579 a h
  have h4 : Entails.eval a c584 := derived584 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c586 := derived586 a h
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c198 := h 197 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c244 := h 243 (by decide)
  have h16 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c152, some c161, some c65, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c152, c161, c65] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c161 := h 160 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨31, by decide⟩, false), (⟨23, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c223, some c222, some c362, some c285, some c221, some c211, some c263, some c315, some c206, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c223, c222, c362, c285, c221, c211, c263, c315, c206] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c223 := h 222 (by decide)
  have h1 : Entails.eval a c222 := h 221 (by decide)
  have h2 : Entails.eval a c362 := h 361 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c211 := h 210 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c127, some c54, some c204, some c201, some c142, some c124, some c253, some c269, some c589, some c161, some c65, some c577, some c353, some c344, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c119, c127, c54, c204, c201, c142, c124, c253, c269, c589, c161, c65, c577, c353, c344] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c127 := h 126 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c253 := h 252 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c589 := derived589 a h
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c577 := derived577 a h
  have h13 : Entails.eval a c353 := h 352 (by decide)
  have h14 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨11, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c588, some c266, some c1, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c546, c588, c266, c1] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c588 := derived588 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨35, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c266, some c265, some c118, some c123, some c221, some c48, some c269, some c211, some c210, some c222, some c283, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c22, c266, c265, c118, c123, c221, c48, c269, c211, c210, c222, c283] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c210 := h 209 (by decide)
  have h10 : Entails.eval a c222 := h 221 (by decide)
  have h11 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c222, some c28, some c211, some c279, some c46, some c475, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c222, c28, c211, c279, c46, c475] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c222 := h 221 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c279 := h 278 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c475 := derived475 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived593

end CochromaticTwenty.Certificates.B16_0_0
