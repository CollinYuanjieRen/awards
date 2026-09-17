import MerLeanExperiment.Certificates.B16_6_0.Steps0000_0099

/-! Generated from the actual pinned b16_6_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c497 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c396, some c489, some c496, some c366, some c384, some c367, some c392, some c433, some c421, some c308, some c60, some c298, some c304, some c46, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked497 : lratChecker f497 p497 = .success := by decide +kernel
theorem unsat497 : Unsatisfiable (PosFin 57) f497 := by
  apply lratCheckerSound f497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p497
  · intro a ha; simp [p497] at ha; subst a; trivial
  · exact checked497
theorem derived497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c497 := by
  apply localUnsat_implies_entails f497 [c390, c396, c489, c496, c366, c384, c367, c392, c433, c421, c308, c60, c298, c304, c46] c497 unsat497 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c489 := derived489 a h
  have h3 : Entails.eval a c496 := derived496 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c384 := h 383 (by decide)
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c392 := h 391 (by decide)
  have h8 : Entails.eval a c433 := derived433 a h
  have h9 : Entails.eval a c421 := derived421 a h
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c304 := h 303 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c498 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨41, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c390, some c366, some c73, some c489, some c497, some c55, some c345, some c435, some c57, some c220, some c106, some c259, some c84, some c46, some c127, some c304, some c181, some c144, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked498 : lratChecker f498 p498 = .success := by decide +kernel
theorem unsat498 : Unsatisfiable (PosFin 57) f498 := by
  apply lratCheckerSound f498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p498
  · intro a ha; simp [p498] at ha; subst a; trivial
  · exact checked498
theorem derived498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c498 := by
  apply localUnsat_implies_entails f498 [c396, c390, c366, c73, c489, c497, c55, c345, c435, c57, c220, c106, c259, c84, c46, c127, c304, c181, c144] c498 unsat498 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c489 := derived489 a h
  have h5 : Entails.eval a c497 := derived497 a h
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c435 := derived435 a h
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c259 := h 258 (by decide)
  have h13 : Entails.eval a c84 := h 83 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c127 := h 126 (by decide)
  have h16 : Entails.eval a c304 := h 303 (by decide)
  have h17 : Entails.eval a c181 := h 180 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c499 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨26, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c308, some c313, some c318, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked499 : lratChecker f499 p499 = .success := by decide +kernel
theorem unsat499 : Unsatisfiable (PosFin 57) f499 := by
  apply lratCheckerSound f499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p499
  · intro a ha; simp [p499] at ha; subst a; trivial
  · exact checked499
theorem derived499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c499 := by
  apply localUnsat_implies_entails f499 [c308, c313, c318] c499 unsat499 (by rfl) a
  have h0 : Entails.eval a c308 := h 307 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c500 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨26, by decide⟩, false), (⟨40, by decide⟩, true), (⟨51, by decide⟩, true), (⟨41, by decide⟩, true), (⟨34, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c73, some c274, some c318, some c329, some c417, some c185, some c158, some c182, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked500 : lratChecker f500 p500 = .success := by decide +kernel
theorem unsat500 : Unsatisfiable (PosFin 57) f500 := by
  apply lratCheckerSound f500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p500
  · intro a ha; simp [p500] at ha; subst a; trivial
  · exact checked500
theorem derived500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c500 := by
  apply localUnsat_implies_entails f500 [c366, c73, c274, c318, c329, c417, c185, c158, c182] c500 unsat500 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c274 := h 273 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c417 := derived417 a h
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c501 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨41, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c390, some c366, some c73, some c489, some c497, some c55, some c345, some c347, some c436, some c498, some c500, some c140, some c421, some c417, some c84, some c279, some c386, some c68, some c332, some c336, some c105, some c385, some c83, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked501 : lratChecker f501 p501 = .success := by decide +kernel
theorem unsat501 : Unsatisfiable (PosFin 57) f501 := by
  apply lratCheckerSound f501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p501
  · intro a ha; simp [p501] at ha; subst a; trivial
  · exact checked501
theorem derived501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c501 := by
  apply localUnsat_implies_entails f501 [c396, c390, c366, c73, c489, c497, c55, c345, c347, c436, c498, c500, c140, c421, c417, c84, c279, c386, c68, c332, c336, c105, c385, c83] c501 unsat501 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c489 := derived489 a h
  have h5 : Entails.eval a c497 := derived497 a h
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  have h9 : Entails.eval a c436 := derived436 a h
  have h10 : Entails.eval a c498 := derived498 a h
  have h11 : Entails.eval a c500 := derived500 a h
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c421 := derived421 a h
  have h14 : Entails.eval a c417 := derived417 a h
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c279 := h 278 (by decide)
  have h17 : Entails.eval a c386 := h 385 (by decide)
  have h18 : Entails.eval a c68 := h 67 (by decide)
  have h19 : Entails.eval a c332 := h 331 (by decide)
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c105 := h 104 (by decide)
  have h22 : Entails.eval a c385 := h 384 (by decide)
  have h23 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c502 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c366, some c73, some c499, some c325, some c309, some c147, some c318, some c182, some c417, some c185, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked502 : lratChecker f502 p502 = .success := by decide +kernel
theorem unsat502 : Unsatisfiable (PosFin 57) f502 := by
  apply lratCheckerSound f502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p502
  · intro a ha; simp [p502] at ha; subst a; trivial
  · exact checked502
theorem derived502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c502 := by
  apply localUnsat_implies_entails f502 [c367, c366, c73, c499, c325, c309, c147, c318, c182, c417, c185] c502 unsat502 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c499 := derived499 a h
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c417 := derived417 a h
  have h10 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c503 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨41, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c390, some c366, some c73, some c489, some c497, some c55, some c345, some c501, some c502, some c498, some c253, some c220, some c124, some c386, some c179, some c84, some c185, some c144, some c421, some c106, some c107, some c417, some c302, some c50, some c320, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked503 : lratChecker f503 p503 = .success := by decide +kernel
theorem unsat503 : Unsatisfiable (PosFin 57) f503 := by
  apply lratCheckerSound f503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p503
  · intro a ha; simp [p503] at ha; subst a; trivial
  · exact checked503
theorem derived503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c503 := by
  apply localUnsat_implies_entails f503 [c396, c390, c366, c73, c489, c497, c55, c345, c501, c502, c498, c253, c220, c124, c386, c179, c84, c185, c144, c421, c106, c107, c417, c302, c50, c320] c503 unsat503 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c489 := derived489 a h
  have h5 : Entails.eval a c497 := derived497 a h
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c501 := derived501 a h
  have h9 : Entails.eval a c502 := derived502 a h
  have h10 : Entails.eval a c498 := derived498 a h
  have h11 : Entails.eval a c253 := h 252 (by decide)
  have h12 : Entails.eval a c220 := h 219 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c386 := h 385 (by decide)
  have h15 : Entails.eval a c179 := h 178 (by decide)
  have h16 : Entails.eval a c84 := h 83 (by decide)
  have h17 : Entails.eval a c185 := h 184 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c421 := derived421 a h
  have h20 : Entails.eval a c106 := h 105 (by decide)
  have h21 : Entails.eval a c107 := h 106 (by decide)
  have h22 : Entails.eval a c417 := derived417 a h
  have h23 : Entails.eval a c302 := h 301 (by decide)
  have h24 : Entails.eval a c50 := h 49 (by decide)
  have h25 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c504 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨35, by decide⟩, true), (⟨1, by decide⟩, false), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c334, some c107, some c385, some c83, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked504 : lratChecker f504 p504 = .success := by decide +kernel
theorem unsat504 : Unsatisfiable (PosFin 57) f504 := by
  apply lratCheckerSound f504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p504
  · intro a ha; simp [p504] at ha; subst a; trivial
  · exact checked504
theorem derived504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c504 := by
  apply localUnsat_implies_entails f504 [c84, c334, c107, c385, c83] c504 unsat504 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c334 := h 333 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c505 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c396, some c489, some c497, some c55, some c345, some c73, some c366, some c503, some c392, some c344, some c367, some c504, some c386, some c495, some c57, some c385, some c106, some c83, some c68, some c105, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 57) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c390, c396, c489, c497, c55, c345, c73, c366, c503, c392, c344, c367, c504, c386, c495, c57, c385, c106, c83, c68, c105] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c489 := derived489 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c503 := derived503 a h
  have h9 : Entails.eval a c392 := h 391 (by decide)
  have h10 : Entails.eval a c344 := h 343 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c504 := derived504 a h
  have h13 : Entails.eval a c386 := h 385 (by decide)
  have h14 : Entails.eval a c495 := derived495 a h
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c106 := h 105 (by decide)
  have h18 : Entails.eval a c83 := h 82 (by decide)
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c68, some c381, some c105, some c83, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 57) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c84, c68, c381, c105, c83] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨45, by decide⟩, false), (⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c506, some c106, some c107, some c57, some c83, some c386, some c379, some c334, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 57) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c506, c106, c107, c57, c83, c386, c379, c334] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c506 := derived506 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c386 := h 385 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, false), (⟨45, by decide⟩, false), (⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c66, some c386, some c111, some c334, some c83, some c379, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 57) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c57, c66, c386, c111, c334, c83, c379] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c386 := h 385 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c334 := h 333 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨35, by decide⟩, true), (⟨56, by decide⟩, true), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c507, some c92, some c93, some c508, some c112, some c84, some c68, some c381, some c111, some c83, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 57) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c507, c92, c93, c508, c112, c84, c68, c381, c111, c83] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c507 := derived507 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c508 := derived508 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c510 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c68, some c381, some c111, some c83, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 57) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c84, c68, c381, c111, c83] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c510, some c112, some c57, some c66, some c380, some c111, some c334, some c83, some c379, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 57) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c510, c112, c57, c66, c380, c111, c334, c83, c379] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c510 := derived510 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c509, some c77, some c511, some c80, some c93, some c504, some c506, some c381, some c107, some c83, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 57) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c509, c77, c511, c80, c93, c504, c506, c381, c107, c83] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c509 := derived509 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c511 := derived511 a h
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c504 := derived504 a h
  have h6 : Entails.eval a c506 := derived506 a h
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c392, some c344, some c512, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 57) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c55, c392, c344, c512] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c392 := h 391 (by decide)
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c512 := derived512 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c514 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨40, by decide⟩, true), (⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c506, some c507, some c106, some c77, some c70, some c511, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked514 : lratChecker f514 p514 = .success := by decide +kernel
theorem unsat514 : Unsatisfiable (PosFin 57) f514 := by
  apply lratCheckerSound f514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p514
  · intro a ha; simp [p514] at ha; subst a; trivial
  · exact checked514
theorem derived514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c514 := by
  apply localUnsat_implies_entails f514 [c506, c507, c106, c77, c70, c511] c514 unsat514 (by rfl) a
  have h0 : Entails.eval a c506 := derived506 a h
  have h1 : Entails.eval a c507 := derived507 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c511 := derived511 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c515 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c512, some c347, some c514, some c92, some c511, some c72, some c70, some c112, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked515 : lratChecker f515 p515 = .success := by decide +kernel
theorem unsat515 : Unsatisfiable (PosFin 57) f515 := by
  apply lratCheckerSound f515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p515
  · intro a ha; simp [p515] at ha; subst a; trivial
  · exact checked515
theorem derived515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c515 := by
  apply localUnsat_implies_entails f515 [c55, c512, c347, c514, c92, c511, c72, c70, c112] c515 unsat515 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c512 := derived512 a h
  have h2 : Entails.eval a c347 := h 346 (by decide)
  have h3 : Entails.eval a c514 := derived514 a h
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c511 := derived511 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c516 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c63, some c92, some c185, some c158, some c15, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked516 : lratChecker f516 p516 = .success := by decide +kernel
theorem unsat516 : Unsatisfiable (PosFin 57) f516 := by
  apply lratCheckerSound f516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p516
  · intro a ha; simp [p516] at ha; subst a; trivial
  · exact checked516
theorem derived516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c516 := by
  apply localUnsat_implies_entails f516 [c63, c92, c185, c158, c15] c516 unsat516 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c517 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨9, by decide⟩, false), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨39, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c293, some c170, some c223, some c116, some c259, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked517 : lratChecker f517 p517 = .success := by decide +kernel
theorem unsat517 : Unsatisfiable (PosFin 57) f517 := by
  apply lratCheckerSound f517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p517
  · intro a ha; simp [p517] at ha; subst a; trivial
  · exact checked517
theorem derived517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c517 := by
  apply localUnsat_implies_entails f517 [c380, c293, c170, c223, c116, c259] c517 unsat517 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c293 := h 292 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c223 := h 222 (by decide)
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c518 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c55, some c390, some c396, some c489, some c345, some c505, some c515, some c361, some c356, some c35, some c92, some c516, some c517, some c57, some c220, some c112, some c259, some c84, some c127, some c172, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked518 : lratChecker f518 p518 = .success := by decide +kernel
theorem unsat518 : Unsatisfiable (PosFin 57) f518 := by
  apply lratCheckerSound f518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p518
  · intro a ha; simp [p518] at ha; subst a; trivial
  · exact checked518
theorem derived518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c518 := by
  apply localUnsat_implies_entails f518 [c497, c55, c390, c396, c489, c345, c505, c515, c361, c356, c35, c92, c516, c517, c57, c220, c112, c259, c84, c127, c172] c518 unsat518 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c396 := h 395 (by decide)
  have h4 : Entails.eval a c489 := derived489 a h
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c505 := derived505 a h
  have h7 : Entails.eval a c515 := derived515 a h
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c516 := derived516 a h
  have h13 : Entails.eval a c517 := derived517 a h
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  have h16 : Entails.eval a c112 := h 111 (by decide)
  have h17 : Entails.eval a c259 := h 258 (by decide)
  have h18 : Entails.eval a c84 := h 83 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  have h20 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c519 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c518, some c497, some c55, some c390, some c396, some c489, some c345, some c505, some c515, some c356, some c57, some c220, some c106, some c259, some c20, some c84, some c127, some c121, some c172, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 57) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c518, c497, c55, c390, c396, c489, c345, c505, c515, c356, c57, c220, c106, c259, c20, c84, c127, c121, c172] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c497 := derived497 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c390 := h 389 (by decide)
  have h4 : Entails.eval a c396 := h 395 (by decide)
  have h5 : Entails.eval a c489 := derived489 a h
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c505 := derived505 a h
  have h8 : Entails.eval a c515 := derived515 a h
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c220 := h 219 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c127 := h 126 (by decide)
  have h17 : Entails.eval a c121 := h 120 (by decide)
  have h18 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c396, some c489, some c497, some c55, some c345, some c505, some c513, some c515, some c356, some c518, some c519, some c380, some c84, some c223, some c421, some c22, some c517, some c121, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 57) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c390, c396, c489, c497, c55, c345, c505, c513, c515, c356, c518, c519, c380, c84, c223, c421, c22, c517, c121] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c489 := derived489 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c505 := derived505 a h
  have h7 : Entails.eval a c513 := derived513 a h
  have h8 : Entails.eval a c515 := derived515 a h
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c518 := derived518 a h
  have h11 : Entails.eval a c519 := derived519 a h
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c84 := h 83 (by decide)
  have h14 : Entails.eval a c223 := h 222 (by decide)
  have h15 : Entails.eval a c421 := derived421 a h
  have h16 : Entails.eval a c22 := h 21 (by decide)
  have h17 : Entails.eval a c517 := derived517 a h
  have h18 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨1, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c496, some c520, some c351, some c390, some c380, some c84, some c106, some c107, some c83, some c69, some c354, some c40, some c294, some c289, some c140, some c170, some c5, some c124, some c119, some c259, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 57) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c496, c520, c351, c390, c380, c84, c106, c107, c83, c69, c354, c40, c294, c289, c140, c170, c5, c124, c119, c259] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c496 := derived496 a h
  have h1 : Entails.eval a c520 := derived520 a h
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c390 := h 389 (by decide)
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c294 := h 293 (by decide)
  have h13 : Entails.eval a c289 := h 288 (by decide)
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c170 := h 169 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c522 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c496, some c520, some c351, some c521, some c57, some c220, some c106, some c259, some c20, some c84, some c381, some c83, some c335, some c354, some c360, some c121, some c172, some c4, some c119, some c145, some c289, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 57) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c496, c520, c351, c521, c57, c220, c106, c259, c20, c84, c381, c83, c335, c354, c360, c121, c172, c4, c119, c145, c289] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c496 := derived496 a h
  have h1 : Entails.eval a c520 := derived520 a h
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c521 := derived521 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c220 := h 219 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c259 := h 258 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c381 := h 380 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c335 := h 334 (by decide)
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c360 := h 359 (by decide)
  have h15 : Entails.eval a c121 := h 120 (by decide)
  have h16 : Entails.eval a c172 := h 171 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c145 := h 144 (by decide)
  have h20 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c523 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c390, some c522, some c92, some c35, some c496, some c520, some c351, some c57, some c220, some c112, some c259, some c84, some c381, some c295, some c335, some c119, some c354, some c172, some c375, some c185, some c181, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 57) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c396, c390, c522, c92, c35, c496, c520, c351, c57, c220, c112, c259, c84, c381, c295, c335, c119, c354, c172, c375, c185, c181] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c522 := derived522 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c496 := derived496 a h
  have h6 : Entails.eval a c520 := derived520 a h
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c220 := h 219 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c381 := h 380 (by decide)
  have h14 : Entails.eval a c295 := h 294 (by decide)
  have h15 : Entails.eval a c335 := h 334 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c172 := h 171 (by decide)
  have h19 : Entails.eval a c375 := h 374 (by decide)
  have h20 : Entails.eval a c185 := h 184 (by decide)
  have h21 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c524 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨9, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c390, some c522, some c92, some c496, some c523, some c380, some c84, some c185, some c14, some c35, some c55, some c520, some c351, some c489, some c239, some c119, some c253, some c278, some c121, some c516, some c264, some c361, some c229, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 57) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c396, c390, c522, c92, c496, c523, c380, c84, c185, c14, c35, c55, c520, c351, c489, c239, c119, c253, c278, c121, c516, c264, c361, c229] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c522 := derived522 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c496 := derived496 a h
  have h5 : Entails.eval a c523 := derived523 a h
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c185 := h 184 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c520 := derived520 a h
  have h13 : Entails.eval a c351 := h 350 (by decide)
  have h14 : Entails.eval a c489 := derived489 a h
  have h15 : Entails.eval a c239 := h 238 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c253 := h 252 (by decide)
  have h18 : Entails.eval a c278 := h 277 (by decide)
  have h19 : Entails.eval a c121 := h 120 (by decide)
  have h20 : Entails.eval a c516 := derived516 a h
  have h21 : Entails.eval a c264 := h 263 (by decide)
  have h22 : Entails.eval a c361 := h 360 (by decide)
  have h23 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c525 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c496, some c523, some c380, some c84, some c390, some c522, some c35, some c293, some c396, some c92, some c55, some c520, some c351, some c185, some c420, some c14, some c524, some c259, some c31, some c124, some c221, some c202, some c363, some c516, some c274, some c278, some c151, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 57) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c496, c523, c380, c84, c390, c522, c35, c293, c396, c92, c55, c520, c351, c185, c420, c14, c524, c259, c31, c124, c221, c202, c363, c516, c274, c278, c151] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c496 := derived496 a h
  have h1 : Entails.eval a c523 := derived523 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c390 := h 389 (by decide)
  have h5 : Entails.eval a c522 := derived522 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c396 := h 395 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c520 := derived520 a h
  have h12 : Entails.eval a c351 := h 350 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c420 := derived420 a h
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c524 := derived524 a h
  have h17 : Entails.eval a c259 := h 258 (by decide)
  have h18 : Entails.eval a c31 := h 30 (by decide)
  have h19 : Entails.eval a c124 := h 123 (by decide)
  have h20 : Entails.eval a c221 := h 220 (by decide)
  have h21 : Entails.eval a c202 := h 201 (by decide)
  have h22 : Entails.eval a c363 := h 362 (by decide)
  have h23 : Entails.eval a c516 := derived516 a h
  have h24 : Entails.eval a c274 := h 273 (by decide)
  have h25 : Entails.eval a c278 := h 277 (by decide)
  have h26 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c520, some c351, some c390, some c396, some c489, some c496, some c523, some c380, some c525, some c170, some c124, some c259, some c253, some c239, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 57) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c520, c351, c390, c396, c489, c496, c523, c380, c525, c170, c124, c259, c253, c239] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c520 := derived520 a h
  have h1 : Entails.eval a c351 := h 350 (by decide)
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c396 := h 395 (by decide)
  have h4 : Entails.eval a c489 := derived489 a h
  have h5 : Entails.eval a c496 := derived496 a h
  have h6 : Entails.eval a c523 := derived523 a h
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c525 := derived525 a h
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c253 := h 252 (by decide)
  have h13 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c386, some c239, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 57) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c383, c386, c239] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c386 := h 385 (by decide)
  have h2 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c528 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, true), (⟨9, by decide⟩, false), (⟨45, by decide⟩, false), (⟨1, by decide⟩, false), (⟨41, by decide⟩, true), (⟨36, by decide⟩, true), (⟨39, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c253, some c527, some c57, some c3, some c20, some c217, some c360, some c164, some c4, some c198, some c64, some c161, some c356, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 57) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c253, c527, c57, c3, c20, c217, c360, c164, c4, c198, c64, c161, c356] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c527 := derived527 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c217 := h 216 (by decide)
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨9, by decide⟩, false), (⟨45, by decide⟩, false), (⟨1, by decide⟩, false), (⟨41, by decide⟩, true), (⟨36, by decide⟩, true), (⟨39, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c528, some c220, some c124, some c383, some c386, some c3, some c199, some c179, some c84, some c119, some c144, some c107, some c327, some c69, some c50, some c289, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 57) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c528, c220, c124, c383, c386, c3, c199, c179, c84, c119, c144, c107, c327, c69, c50, c289] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c528 := derived528 a h
  have h1 : Entails.eval a c220 := h 219 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c386 := h 385 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c327 := h 326 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c390, some c526, some c366, some c73, some c520, some c351, some c489, some c529, some c259, some c220, some c124, some c383, some c386, some c3, some c84, some c107, some c22, some c69, some c217, some c360, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 57) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c396, c390, c526, c366, c73, c520, c351, c489, c529, c259, c220, c124, c383, c386, c3, c84, c107, c22, c69, c217, c360] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c526 := derived526 a h
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c520 := derived520 a h
  have h6 : Entails.eval a c351 := h 350 (by decide)
  have h7 : Entails.eval a c489 := derived489 a h
  have h8 : Entails.eval a c529 := derived529 a h
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c383 := h 382 (by decide)
  have h13 : Entails.eval a c386 := h 385 (by decide)
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c22 := h 21 (by decide)
  have h18 : Entails.eval a c69 := h 68 (by decide)
  have h19 : Entails.eval a c217 := h 216 (by decide)
  have h20 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c220, some c124, some c179, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 57) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c220, c124, c179] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c220 := h 219 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c390, some c489, some c520, some c351, some c526, some c73, some c366, some c530, some c140, some c185, some c531, some c259, some c253, some c527, some c57, some c106, some c20, some c217, some c278, some c46, some c274, some c55, some c122, some c175, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 57) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c396, c390, c489, c520, c351, c526, c73, c366, c530, c140, c185, c531, c259, c253, c527, c57, c106, c20, c217, c278, c46, c274, c55, c122, c175] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c489 := derived489 a h
  have h3 : Entails.eval a c520 := derived520 a h
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c526 := derived526 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c530 := derived530 a h
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c531 := derived531 a h
  have h12 : Entails.eval a c259 := h 258 (by decide)
  have h13 : Entails.eval a c253 := h 252 (by decide)
  have h14 : Entails.eval a c527 := derived527 a h
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c106 := h 105 (by decide)
  have h17 : Entails.eval a c20 := h 19 (by decide)
  have h18 : Entails.eval a c217 := h 216 (by decide)
  have h19 : Entails.eval a c278 := h 277 (by decide)
  have h20 : Entails.eval a c46 := h 45 (by decide)
  have h21 : Entails.eval a c274 := h 273 (by decide)
  have h22 : Entails.eval a c55 := h 54 (by decide)
  have h23 : Entails.eval a c122 := h 121 (by decide)
  have h24 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨23, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c532, some c396, some c366, some c486, some c110, some c456, some c73, some c103, some c104, some c351, some c223, some c127, some c181, some c185, some c1, some c5, some c200, some c485, some c194, some c348, some c166, some c159, some c362, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 57) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c390, c532, c396, c366, c486, c110, c456, c73, c103, c104, c351, c223, c127, c181, c185, c1, c5, c200, c485, c194, c348, c166, c159, c362] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c532 := derived532 a h
  have h2 : Entails.eval a c396 := h 395 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c486 := derived486 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c456 := derived456 a h
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c223 := h 222 (by decide)
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c181 := h 180 (by decide)
  have h14 : Entails.eval a c185 := h 184 (by decide)
  have h15 : Entails.eval a c1 := h 0 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c200 := h 199 (by decide)
  have h18 : Entails.eval a c485 := derived485 a h
  have h19 : Entails.eval a c194 := h 193 (by decide)
  have h20 : Entails.eval a c348 := h 347 (by decide)
  have h21 : Entails.eval a c166 := h 165 (by decide)
  have h22 : Entails.eval a c159 := h 158 (by decide)
  have h23 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c532, some c390, some c366, some c486, some c110, some c39, some c73, some c103, some c104, some c533, some c57, some c66, some c386, some c527, some c302, some c18, some c26, some c47, some c217, some c246, some c275, some c305, some c207, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 57) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c396, c532, c390, c366, c486, c110, c39, c73, c103, c104, c533, c57, c66, c386, c527, c302, c18, c26, c47, c217, c246, c275, c305, c207] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c532 := derived532 a h
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c486 := derived486 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c533 := derived533 a h
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c386 := h 385 (by decide)
  have h14 : Entails.eval a c527 := derived527 a h
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c18 := h 17 (by decide)
  have h17 : Entails.eval a c26 := h 25 (by decide)
  have h18 : Entails.eval a c47 := h 46 (by decide)
  have h19 : Entails.eval a c217 := h 216 (by decide)
  have h20 : Entails.eval a c246 := h 245 (by decide)
  have h21 : Entails.eval a c275 := h 274 (by decide)
  have h22 : Entails.eval a c305 := h 304 (by decide)
  have h23 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c358, some c159, some c69, some c4, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 57) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c356, c358, c159, c69, c4] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨44, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c532, some c390, some c73, some c396, some c366, some c534, some c259, some c486, some c110, some c39, some c302, some c116, some c179, some c185, some c1, some c103, some c104, some c47, some c383, some c66, some c535, some c217, some c18, some c435, some c122, some c279, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 57) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c532, c390, c73, c396, c366, c534, c259, c486, c110, c39, c302, c116, c179, c185, c1, c103, c104, c47, c383, c66, c535, c217, c18, c435, c122, c279] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c532 := derived532 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c396 := h 395 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c534 := derived534 a h
  have h6 : Entails.eval a c259 := h 258 (by decide)
  have h7 : Entails.eval a c486 := derived486 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c302 := h 301 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c179 := h 178 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c104 := h 103 (by decide)
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c383 := h 382 (by decide)
  have h19 : Entails.eval a c66 := h 65 (by decide)
  have h20 : Entails.eval a c535 := derived535 a h
  have h21 : Entails.eval a c217 := h 216 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c435 := derived435 a h
  have h24 : Entails.eval a c122 := h 121 (by decide)
  have h25 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c534, some c396, some c390, some c366, some c73, some c383, some c386, some c536, some c351, some c60, some c331, some c22, some c357, some c217, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 57) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c534, c396, c390, c366, c73, c383, c386, c536, c351, c60, c331, c22, c357, c217] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c534 := derived534 a h
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c386 := h 385 (by decide)
  have h7 : Entails.eval a c536 := derived536 a h
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c331 := h 330 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c532, some c390, some c73, some c103, some c104, some c537, some c85, some c534, some c259, some c396, some c366, some c486, some c110, some c456, some c217, some c22, some c268, some c485, some c243, some c385, some c367, some c329, some c349, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 57) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c532, c390, c73, c103, c104, c537, c85, c534, c259, c396, c366, c486, c110, c456, c217, c22, c268, c485, c243, c385, c367, c329, c349] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c532 := derived532 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c537 := derived537 a h
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c534 := derived534 a h
  have h8 : Entails.eval a c259 := h 258 (by decide)
  have h9 : Entails.eval a c396 := h 395 (by decide)
  have h10 : Entails.eval a c366 := h 365 (by decide)
  have h11 : Entails.eval a c486 := derived486 a h
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c456 := derived456 a h
  have h14 : Entails.eval a c217 := h 216 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c485 := derived485 a h
  have h18 : Entails.eval a c243 := h 242 (by decide)
  have h19 : Entails.eval a c385 := h 384 (by decide)
  have h20 : Entails.eval a c367 := h 366 (by decide)
  have h21 : Entails.eval a c329 := h 328 (by decide)
  have h22 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c532, some c390, some c73, some c104, some c537, some c57, some c538, some c357, some c351, some c396, some c366, some c486, some c110, some c39, some c103, some c60, some c485, some c304, some c358, some c49, some c275, some c140, some c1, some c160, some c159, some c200, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 57) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c532, c390, c73, c104, c537, c57, c538, c357, c351, c396, c366, c486, c110, c39, c103, c60, c485, c304, c358, c49, c275, c140, c1, c160, c159, c200] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c532 := derived532 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c537 := derived537 a h
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c538 := derived538 a h
  have h7 : Entails.eval a c357 := h 356 (by decide)
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c396 := h 395 (by decide)
  have h10 : Entails.eval a c366 := h 365 (by decide)
  have h11 : Entails.eval a c486 := derived486 a h
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c485 := derived485 a h
  have h17 : Entails.eval a c304 := h 303 (by decide)
  have h18 : Entails.eval a c358 := h 357 (by decide)
  have h19 : Entails.eval a c49 := h 48 (by decide)
  have h20 : Entails.eval a c275 := h 274 (by decide)
  have h21 : Entails.eval a c140 := h 139 (by decide)
  have h22 : Entails.eval a c1 := h 0 (by decide)
  have h23 : Entails.eval a c160 := h 159 (by decide)
  have h24 : Entails.eval a c159 := h 158 (by decide)
  have h25 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c532, some c396, some c390, some c73, some c366, some c104, some c103, some c486, some c110, some c456, some c537, some c85, some c539, some c107, some c88, some c101, some c385, some c395, some c367, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 57) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c532, c396, c390, c73, c366, c104, c103, c486, c110, c456, c537, c85, c539, c107, c88, c101, c385, c395, c367] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c532 := derived532 a h
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c486 := derived486 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c456 := derived456 a h
  have h10 : Entails.eval a c537 := derived537 a h
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c539 := derived539 a h
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c101 := h 100 (by decide)
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c395 := h 394 (by decide)
  have h18 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c88, some c379, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 57) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c85, c88, c379] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c540, some c532, some c104, some c103, some c541, some c396, some c390, some c486, some c110, some c39, some c456, some c101, some c395, some c302, some c47, some c50, some c320, some c326, some c309, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 57) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c540, c532, c104, c103, c541, c396, c390, c486, c110, c39, c456, c101, c395, c302, c47, c50, c320, c326, c309] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c540 := derived540 a h
  have h1 : Entails.eval a c532 := derived532 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c541 := derived541 a h
  have h5 : Entails.eval a c396 := h 395 (by decide)
  have h6 : Entails.eval a c390 := h 389 (by decide)
  have h7 : Entails.eval a c486 := derived486 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c456 := derived456 a h
  have h11 : Entails.eval a c101 := h 100 (by decide)
  have h12 : Entails.eval a c395 := h 394 (by decide)
  have h13 : Entails.eval a c302 := h 301 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c320 := h 319 (by decide)
  have h17 : Entails.eval a c326 := h 325 (by decide)
  have h18 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c103, some c107, some c541, some c293, some c140, some c308, some c1, some c5, some c325, some c327, some c151, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 57) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c104, c103, c107, c541, c293, c140, c308, c1, c5, c325, c327, c151] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c541 := derived541 a h
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c140 := h 139 (by decide)
  have h6 : Entails.eval a c308 := h 307 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c327 := h 326 (by decide)
  have h11 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c103, some c104, some c543, some c47, some c50, some c326, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 57) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c107, c103, c104, c543, c47, c50, c326] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c545 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c532, some c103, some c104, some c540, some c396, some c390, some c107, some c541, some c542, some c77, some c110, some c544, some c51, some c293, some c140, some c308, some c1, some c5, some c327, some c324, some c151, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 57) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c532, c103, c104, c540, c396, c390, c107, c541, c542, c77, c110, c544, c51, c293, c140, c308, c1, c5, c327, c324, c151] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c532 := derived532 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c540 := derived540 a h
  have h4 : Entails.eval a c396 := h 395 (by decide)
  have h5 : Entails.eval a c390 := h 389 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c541 := derived541 a h
  have h8 : Entails.eval a c542 := derived542 a h
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c544 := derived544 a h
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c1 := h 0 (by decide)
  have h17 : Entails.eval a c5 := h 4 (by decide)
  have h18 : Entails.eval a c327 := h 326 (by decide)
  have h19 : Entails.eval a c324 := h 323 (by decide)
  have h20 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c327, some c321, some c308, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 57) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c327, c321, c308] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c327 := h 326 (by decide)
  have h1 : Entails.eval a c321 := h 320 (by decide)
  have h2 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c545, some c532, some c104, some c70, some c72, some c351, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 57) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c545, c532, c104, c70, c72, c351] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c545 := derived545 a h
  have h1 : Entails.eval a c532 := derived532 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c47, some c49, some c546, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 57) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c47, c49, c546] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c47 := h 46 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c546 := derived546 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c396, some c532, some c104, some c103, some c545, some c548, some c485, some c547, some c284, some c51, some c53, some c546, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 57) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c390, c396, c532, c104, c103, c545, c548, c485, c547, c284, c51, c53, c546] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c532 := derived532 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c545 := derived545 a h
  have h6 : Entails.eval a c548 := derived548 a h
  have h7 : Entails.eval a c485 := derived485 a h
  have h8 : Entails.eval a c547 := derived547 a h
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c546 := derived546 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨27, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c147, some c320, some c318, some c17, some c9, some c150, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 57) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c309, c147, c320, c318, c17, c9, c150] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c318, some c310, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 57) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c320, c318, c310] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c460, some c392, some c551, some c140, some c1, some c4, some c187, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 57) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c460, c392, c551, c140, c1, c4, c187] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c460 := derived460 a h
  have h1 : Entails.eval a c392 := h 391 (by decide)
  have h2 : Entails.eval a c551 := derived551 a h
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c532, some c396, some c390, some c104, some c103, some c545, some c485, some c548, some c549, some c110, some c39, some c77, some c456, some c542, some c552, some c550, some c305, some c284, some c326, some c323, some c224, some c26, some c34, some c208, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 57) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c532, c396, c390, c104, c103, c545, c485, c548, c549, c110, c39, c77, c456, c542, c552, c550, c305, c284, c326, c323, c224, c26, c34, c208] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c532 := derived532 a h
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c545 := derived545 a h
  have h6 : Entails.eval a c485 := derived485 a h
  have h7 : Entails.eval a c548 := derived548 a h
  have h8 : Entails.eval a c549 := derived549 a h
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c456 := derived456 a h
  have h13 : Entails.eval a c542 := derived542 a h
  have h14 : Entails.eval a c552 := derived552 a h
  have h15 : Entails.eval a c550 := derived550 a h
  have h16 : Entails.eval a c305 := h 304 (by decide)
  have h17 : Entails.eval a c284 := h 283 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c323 := h 322 (by decide)
  have h20 : Entails.eval a c224 := h 223 (by decide)
  have h21 : Entails.eval a c26 := h 25 (by decide)
  have h22 : Entails.eval a c34 := h 33 (by decide)
  have h23 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c396, some c532, some c540, some c553, some c35, some c92, some c109, some c110, some c486, some c93, some c460, some c375, some c379, some c294, some c371, some c316, some c392, some c310, some c319, some c325, some c51, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 57) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c390, c396, c532, c540, c553, c35, c92, c109, c110, c486, c93, c460, c375, c379, c294, c371, c316, c392, c310, c319, c325, c51] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c532 := derived532 a h
  have h3 : Entails.eval a c540 := derived540 a h
  have h4 : Entails.eval a c553 := derived553 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c486 := derived486 a h
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c460 := derived460 a h
  have h12 : Entails.eval a c375 := h 374 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c294 := h 293 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c316 := h 315 (by decide)
  have h17 : Entails.eval a c392 := h 391 (by decide)
  have h18 : Entails.eval a c310 := h 309 (by decide)
  have h19 : Entails.eval a c319 := h 318 (by decide)
  have h20 : Entails.eval a c325 := h 324 (by decide)
  have h21 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨25, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c319, some c311, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 57) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c546, c319, c311] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c551, some c555, some c47, some c51, some c111, some c108, some c94, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 57) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c551, c555, c47, c51, c111, c108, c94] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c551 := derived551 a h
  have h1 : Entails.eval a c555 := derived555 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c95, some c94, some c107, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 57) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c95, c94, c107] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c95 := h 94 (by decide)
  have h1 : Entails.eval a c94 := h 93 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c35, some c140, some c308, some c400, some c324, some c51, some c557, some c110, some c1, some c101, some c187, some c4, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c556, c35, c140, c308, c400, c324, c51, c557, c110, c1, c101, c187, c4] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c308 := h 307 (by decide)
  have h4 : Entails.eval a c400 := derived400 a h
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c557 := derived557 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c308, some c400, some c325, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c140, c308, c400, c325] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c400 := derived400 a h
  have h3 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c558, some c557, some c103, some c559, some c551, some c555, some c47, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c558, c557, c103, c559, c551, c555, c47] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c558 := derived558 a h
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c559 := derived559 a h
  have h4 : Entails.eval a c551 := derived551 a h
  have h5 : Entails.eval a c555 := derived555 a h
  have h6 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c368, some c381, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c369, c368, c381] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c560, some c35, some c73, some c561, some c291, some c311, some c310, some c322, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c560, c35, c73, c561, c291, c311, c310, c322] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c560 := derived560 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c561 := derived561 a h
  have h4 : Entails.eval a c291 := h 290 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c310 := h 309 (by decide)
  have h7 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c392, some c395, some c562, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c392, c395, c562] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c392 := h 391 (by decide)
  have h1 : Entails.eval a c395 := h 394 (by decide)
  have h2 : Entails.eval a c562 := derived562 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c372, some c377, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c369, c372, c377] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c73, some c564, some c295, some c311, some c314, some c318, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c35, c73, c564, c295, c311, c314, c318] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c564 := derived564 a h
  have h3 : Entails.eval a c295 := h 294 (by decide)
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c107, some c98, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c105, c107, c98] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨50, by decide⟩, true), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c563, some c565, some c566, some c562, some c88, some c59, some c419, some c355, some c103, some c456, some c75, some c110, some c61, some c382, some c369, some c380, some c386, some c366, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c563, c565, c566, c562, c88, c59, c419, c355, c103, c456, c75, c110, c61, c382, c369, c380, c386, c366] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c563 := derived563 a h
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c566 := derived566 a h
  have h3 : Entails.eval a c562 := derived562 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c419 := derived419 a h
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c456 := derived456 a h
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c369 := h 368 (by decide)
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c386 := h 385 (by decide)
  have h17 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c565, some c566, some c98, some c75, some c37, some c300, some c50, some c546, some c555, some c146, some c140, some c5, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c565, c566, c98, c75, c37, c300, c50, c546, c555, c146, c140, c5] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c565 := derived565 a h
  have h1 : Entails.eval a c566 := derived566 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c546 := derived546 a h
  have h8 : Entails.eval a c555 := derived555 a h
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c563, some c565, some c567, some c568, some c103, some c36, some c74, some c499, some c298, some c366, some c371, some c377, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c563, c565, c567, c568, c103, c36, c74, c499, c298, c366, c371, c377] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c563 := derived563 a h
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c568 := derived568 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c499 := derived499 a h
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨43, by decide⟩, false), (⟨2, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c366, some c433, some c140, some c308, some c417, some c298, some c300, some c45, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c379, c366, c433, c140, c308, c417, c298, c300, c45] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c433 := derived433 a h
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c417 := derived417 a h
  have h6 : Entails.eval a c298 := h 297 (by decide)
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨2, by decide⟩, true), (⟨46, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c563, some c566, some c569, some c379, some c385, some c366, some c570, some c55, some c345, some c347, some c57, some c69, some c329, some c386, some c360, some c338, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c554, c563, c566, c569, c379, c385, c366, c570, c55, c345, c347, c57, c69, c329, c386, c360, c338] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c563 := derived563 a h
  have h2 : Entails.eval a c566 := derived566 a h
  have h3 : Entails.eval a c569 := derived569 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c570 := derived570 a h
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c347 := h 346 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  have h14 : Entails.eval a c386 := h 385 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨46, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c569, some c563, some c103, some c571, some c372, some c371, some c386, some c57, some c345, some c55, some c433, some c384, some c140, some c491, some c2, some c122, some c190, some c175, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c554, c569, c563, c103, c571, c372, c371, c386, c57, c345, c55, c433, c384, c140, c491, c2, c122, c190, c175] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c569 := derived569 a h
  have h2 : Entails.eval a c563 := derived563 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c571 := derived571 a h
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c386 := h 385 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c433 := derived433 a h
  have h12 : Entails.eval a c384 := h 383 (by decide)
  have h13 : Entails.eval a c140 := h 139 (by decide)
  have h14 : Entails.eval a c491 := derived491 a h
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c190 := h 189 (by decide)
  have h18 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c563, some c566, some c572, some c98, some c75, some c97, some c37, some c379, some c385, some c571, some c300, some c366, some c110, some c50, some c89, some c546, some c302, some c146, some c144, some c14, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c554, c563, c566, c572, c98, c75, c97, c37, c379, c385, c571, c300, c366, c110, c50, c89, c546, c302, c146, c144, c14] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c563 := derived563 a h
  have h2 : Entails.eval a c566 := derived566 a h
  have h3 : Entails.eval a c572 := derived572 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c379 := h 378 (by decide)
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c571 := derived571 a h
  have h11 : Entails.eval a c300 := h 299 (by decide)
  have h12 : Entails.eval a c366 := h 365 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c546 := derived546 a h
  have h17 : Entails.eval a c302 := h 301 (by decide)
  have h18 : Entails.eval a c146 := h 145 (by decide)
  have h19 : Entails.eval a c144 := h 143 (by decide)
  have h20 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c569, some c563, some c566, some c573, some c78, some c59, some c419, some c355, some c103, some c456, some c110, some c70, some c75, some c37, some c61, some c345, some c382, some c301, some c218, some c51, some c18, some c255, some c226, some c207, some c276, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c554, c569, c563, c566, c573, c78, c59, c419, c355, c103, c456, c110, c70, c75, c37, c61, c345, c382, c301, c218, c51, c18, c255, c226, c207, c276] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c569 := derived569 a h
  have h2 : Entails.eval a c563 := derived563 a h
  have h3 : Entails.eval a c566 := derived566 a h
  have h4 : Entails.eval a c573 := derived573 a h
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c419 := derived419 a h
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c456 := derived456 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c345 := h 344 (by decide)
  have h17 : Entails.eval a c382 := h 381 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c218 := h 217 (by decide)
  have h20 : Entails.eval a c51 := h 50 (by decide)
  have h21 : Entails.eval a c18 := h 17 (by decide)
  have h22 : Entails.eval a c255 := h 254 (by decide)
  have h23 : Entails.eval a c226 := h 225 (by decide)
  have h24 : Entails.eval a c207 := h 206 (by decide)
  have h25 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c75, some c37, some c292, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c75, c37, c292] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c292, some c314, some c313, some c142, some c327, some c322, some c169, some c50, some c185, some c111, some c10, some c51, some c154, some c325, some c202, some c150, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c575, c292, c314, c313, c142, c327, c322, c169, c50, c185, c111, c10, c51, c154, c325, c202, c150] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c292 := h 291 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c327 := h 326 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c154 := h 153 (by decide)
  have h14 : Entails.eval a c325 := h 324 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c563, some c574, some c35, some c73, some c92, some c576, some c372, some c295, some c41, some c146, some c172, some c14, some c185, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c554, c563, c574, c35, c73, c92, c576, c372, c295, c41, c146, c172, c14, c185] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c563 := derived563 a h
  have h2 : Entails.eval a c574 := derived574 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c576 := derived576 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c73, some c92, some c93, some c575, some c576, some c110, some c111, some c372, some c419, some c381, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c35, c73, c92, c93, c575, c576, c110, c111, c372, c419, c381] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c575 := derived575 a h
  have h5 : Entails.eval a c576 := derived576 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c419 := derived419 a h
  have h10 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c577, some c578, some c566, some c372, some c371, some c75, some c386, some c103, some c57, some c88, some c381, some c367, some c502, some c384, some c36, some c55, some c345, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c554, c577, c578, c566, c372, c371, c75, c386, c103, c57, c88, c381, c367, c502, c384, c36, c55, c345] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c577 := derived577 a h
  have h2 : Entails.eval a c578 := derived578 a h
  have h3 : Entails.eval a c566 := derived566 a h
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c371 := h 370 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c386 := h 385 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c381 := h 380 (by decide)
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c502 := derived502 a h
  have h14 : Entails.eval a c384 := h 383 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c55 := h 54 (by decide)
  have h17 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c419, some c103, some c456, some c110, some c37, some c42, some c301, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c385, c419, c103, c456, c110, c37, c42, c301] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c419 := derived419 a h
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c456 := derived456 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c577, some c554, some c578, some c566, some c579, some c580, some c367, some c376, some c381, some c380, some c88, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c577, c554, c578, c566, c579, c580, c367, c376, c381, c380, c88] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c577 := derived577 a h
  have h1 : Entails.eval a c554 := derived554 a h
  have h2 : Entails.eval a c578 := derived578 a h
  have h3 : Entails.eval a c566 := derived566 a h
  have h4 : Entails.eval a c579 := derived579 a h
  have h5 : Entails.eval a c580 := derived580 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c381 := h 380 (by decide)
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c419, some c88, some c103, some c380, some c79, some c544, some c317, some c309, some c321, some c292, some c47, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c379, c419, c88, c103, c380, c79, c544, c317, c309, c321, c292, c47] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c419 := derived419 a h
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c544 := derived544 a h
  have h7 : Entails.eval a c317 := h 316 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c321 := h 320 (by decide)
  have h10 : Entails.eval a c292 := h 291 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨55, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c582, some c105, some c107, some c548, some c41, some c292, some c546, some c140, some c309, some c4, some c326, some c323, some c154, some c150, some c197, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c582, c105, c107, c548, c41, c292, c546, c140, c309, c4, c326, c323, c154, c150, c197] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c582 := derived582 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c548 := derived548 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c546 := derived546 a h
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c150 := h 149 (by decide)
  have h14 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c583, some c367, some c366, some c105, some c107, some c102, some c548, some c41, some c79, some c301, some c304, some c147, some c39, some c144, some c15, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c583, c367, c366, c105, c107, c102, c548, c41, c79, c301, c304, c147, c39, c144, c15] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c548 := derived548 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c144 := h 143 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c581, some c577, some c554, some c583, some c366, some c367, some c382, some c385, some c584, some c419, some c88, some c78, some c59, some c103, some c386, some c348, some c369, some c66, some c345, some c331, some c218, some c359, some c18, some c217, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c581, c577, c554, c583, c366, c367, c382, c385, c584, c419, c88, c78, c59, c103, c386, c348, c369, c66, c345, c331, c218, c359, c18, c217] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c581 := derived581 a h
  have h1 : Entails.eval a c577 := derived577 a h
  have h2 : Entails.eval a c554 := derived554 a h
  have h3 : Entails.eval a c583 := derived583 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c584 := derived584 a h
  have h9 : Entails.eval a c419 := derived419 a h
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c386 := h 385 (by decide)
  have h15 : Entails.eval a c348 := h 347 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c66 := h 65 (by decide)
  have h18 : Entails.eval a c345 := h 344 (by decide)
  have h19 : Entails.eval a c331 := h 330 (by decide)
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c359 := h 358 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨39, by decide⟩, false), (⟨35, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c358, some c69, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c359, c358, c69] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c79, some c585, some c56, some c85, some c581, some c577, some c369, some c344, some c331, some c55, some c218, some c18, some c253, some c586, some c217, some c121, some c544, some c170, some c317, some c116, some c546, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c554, c79, c585, c56, c85, c581, c577, c369, c344, c331, c55, c218, c18, c253, c586, c217, c121, c544, c170, c317, c116, c546] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c585 := derived585 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c581 := derived581 a h
  have h6 : Entails.eval a c577 := derived577 a h
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c331 := h 330 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c218 := h 217 (by decide)
  have h12 : Entails.eval a c18 := h 17 (by decide)
  have h13 : Entails.eval a c253 := h 252 (by decide)
  have h14 : Entails.eval a c586 := derived586 a h
  have h15 : Entails.eval a c217 := h 216 (by decide)
  have h16 : Entails.eval a c121 := h 120 (by decide)
  have h17 : Entails.eval a c544 := derived544 a h
  have h18 : Entails.eval a c170 := h 169 (by decide)
  have h19 : Entails.eval a c317 := h 316 (by decide)
  have h20 : Entails.eval a c116 := h 115 (by decide)
  have h21 : Entails.eval a c546 := derived546 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c378, some c366, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c383, c378, c366] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c585, some c85, some c588, some c587, some c380, some c386, some c366, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c585, c85, c588, c587, c380, c386, c366] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c585 := derived585 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c588 := derived588 a h
  have h3 : Entails.eval a c587 := derived587 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c386 := h 385 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c419, some c379, some c55, some c74, some c581, some c345, some c495, some c344, some c69, some c513, some c219, some c360, some c19, some c121, some c2, some c170, some c161, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c103, c419, c379, c55, c74, c581, c345, c495, c344, c69, c513, c219, c360, c19, c121, c2, c170, c161] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c419 := derived419 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c581 := derived581 a h
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c495 := derived495 a h
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c513 := derived513 a h
  have h11 : Entails.eval a c219 := h 218 (by decide)
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c121 := h 120 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c84, some c74, some c590, some c38, some c406, some c414, some c546, some c140, some c308, some c392, some c2, some c5, some c324, some c309, some c153, some c45, some c326, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c103, c84, c74, c590, c38, c406, c414, c546, c140, c308, c392, c2, c5, c324, c309, c153, c45, c326] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c590 := derived590 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c406 := derived406 a h
  have h6 : Entails.eval a c414 := derived414 a h
  have h7 : Entails.eval a c546 := derived546 a h
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c392 := h 391 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c324 := h 323 (by decide)
  have h14 : Entails.eval a c309 := h 308 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c35, some c92, some c406, some c554, some c577, some c581, some c369, some c93, some c110, some c419, some c55, some c379, some c294, some c495, some c50, some c293, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c591, c35, c92, c406, c554, c577, c581, c369, c93, c110, c419, c55, c379, c294, c495, c50, c293] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c406 := derived406 a h
  have h4 : Entails.eval a c554 := derived554 a h
  have h5 : Entails.eval a c577 := derived577 a h
  have h6 : Entails.eval a c581 := derived581 a h
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c419 := derived419 a h
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c379 := h 378 (by decide)
  have h13 : Entails.eval a c294 := h 293 (by decide)
  have h14 : Entails.eval a c495 := derived495 a h
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c406, some c554, some c393, some c565, some c74, some c561, some c395, some c108, some c93, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c35, c406, c554, c393, c565, c74, c561, c395, c108, c93] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c406 := derived406 a h
  have h2 : Entails.eval a c554 := derived554 a h
  have h3 : Entails.eval a c393 := h 392 (by decide)
  have h4 : Entails.eval a c565 := derived565 a h
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c561 := derived561 a h
  have h7 : Entails.eval a c395 := h 394 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c593, some c103, some c83, some c74, some c55, some c379, some c393, some c394, some c346, some c99, some c76, some c406, some c140, some c2, some c170, some c171, some c189, some c193, some c344, some c219, some c162, some c252, some c256, some c203, some c131, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c593, c103, c83, c74, c55, c379, c393, c394, c346, c99, c76, c406, c140, c2, c170, c171, c189, c193, c344, c219, c162, c252, c256, c203, c131] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c593 := derived593 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c393 := h 392 (by decide)
  have h7 : Entails.eval a c394 := h 393 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c406 := derived406 a h
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  have h15 : Entails.eval a c171 := h 170 (by decide)
  have h16 : Entails.eval a c189 := h 188 (by decide)
  have h17 : Entails.eval a c193 := h 192 (by decide)
  have h18 : Entails.eval a c344 := h 343 (by decide)
  have h19 : Entails.eval a c219 := h 218 (by decide)
  have h20 : Entails.eval a c162 := h 161 (by decide)
  have h21 : Entails.eval a c252 := h 251 (by decide)
  have h22 : Entails.eval a c256 := h 255 (by decide)
  have h23 : Entails.eval a c203 := h 202 (by decide)
  have h24 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨41, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c380, some c88, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c381, c380, c88] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c595, some c592, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c595, c592] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c595 := derived595 a h
  have h1 : Entails.eval a c592 := derived592 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived596

end CochromaticTwenty.Certificates.B16_6_0
