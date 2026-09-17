import MerLeanExperiment.Certificates.Z12Direct_5_8_10.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_8_10-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_10
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c429 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c421, some c428, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p429 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 31) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c421, c428] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c421 := derived421 a h
  have h1 : Entails.eval a c428 := derived428 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c430 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c429, some c56, some c52, some c3, some c216, some c140, some c84, some c25, some c308, some c67, some c370, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p430 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 31) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c407, c429, c56, c52, c3, c216, c140, c84, c25, c308, c67, c370] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c370 := derived370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c431 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c429, some c52, some c56, some c430, some c219, some c143, some c87, some c25, some c86, some c140, some c216, some c307, some c136, some c69, some c71, some c134, some c18, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p431 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 31) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c407, c429, c52, c56, c430, c219, c143, c87, c25, c86, c140, c216, c307, c136, c69, c71, c134, c18] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c430 := derived430 a h
  have h5 : Entails.eval a c219 := h 218 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  have h12 : Entails.eval a c307 := h 306 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c134 := h 133 (by decide)
  have h17 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c432 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c56, some c52, some c431, some c3, some c219, some c143, some c89, some c25, some c307, some c75, some c105, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p432 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 31) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c407, c56, c52, c431, c3, c219, c143, c89, c25, c307, c75, c105] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c431 := derived431 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c219 := h 218 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c52, some c56, some c432, some c216, some c140, some c86, some c25, some c89, some c143, some c219, some c308, some c67, some c370, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p433 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 31) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c407, c52, c56, c432, c216, c140, c86, c25, c89, c143, c219, c308, c67, c370] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c432 := derived432 a h
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c140 := h 139 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c308 := h 307 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c370 := derived370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c67, some c370, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p434 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 31) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c67, c370] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c370 := derived370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c435 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c156, some c232, some c51, some c94, some c24, some c23, some c304, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p435 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 31) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c407, c156, c232, c51, c94, c24, c23, c304] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c433, some c435, some c65, some c67, some c434, some c320, some c158, some c55, some c234, some c313, some c310, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p436 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 31) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c407, c433, c435, c65, c67, c434, c320, c158, c55, c234, c313, c310] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c435 := derived435 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c434 := derived434 a h
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c234 := h 233 (by decide)
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c433, some c158, some c55, some c234, some c154, some c5, some c230, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p437 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 31) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c407, c433, c158, c55, c234, c154, c5, c230] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c234 := h 233 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c438 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c433, some c436, some c437, some c308, some c218, some c305, some c306, some c346, some c112, some c321, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p438 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 31) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c407, c433, c436, c437, c308, c218, c305, c306, c346, c112, c321] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c306 := h 305 (by decide)
  have h8 : Entails.eval a c346 := derived346 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c437, some c433, some c431, some c387, some c346, some c298, some c391, some c14, some c179, some c112, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p439 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 31) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c407, c437, c433, c431, c387, c346, c298, c391, c14, c179, c112] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c437 := derived437 a h
  have h2 : Entails.eval a c433 := derived433 a h
  have h3 : Entails.eval a c431 := derived431 a h
  have h4 : Entails.eval a c387 := derived387 a h
  have h5 : Entails.eval a c346 := derived346 a h
  have h6 : Entails.eval a c298 := h 297 (by decide)
  have h7 : Entails.eval a c391 := derived391 a h
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c440 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c139, some c85, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p440 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 31) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c139, c85] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c139 := h 138 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c441 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c433, some c431, some c57, some c59, some c73, some c192, some c390, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p441 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 31) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c433, c431, c57, c59, c73, c192, c390] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c433 := derived433 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c390 := derived390 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨23, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c209, some c37, some c272, some c291, some c318, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p442 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 31) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c407, c209, c37, c272, c291, c318] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c209 := h 208 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c443 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c433, some c431, some c438, some c440, some c387, some c346, some c439, some c441, some c306, some c442, some c75, some c122, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p443 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 31) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c433, c431, c438, c440, c387, c346, c439, c441, c306, c442, c75, c122] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c433 := derived433 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c438 := derived438 a h
  have h3 : Entails.eval a c440 := derived440 a h
  have h4 : Entails.eval a c387 := derived387 a h
  have h5 : Entails.eval a c346 := derived346 a h
  have h6 : Entails.eval a c439 := derived439 a h
  have h7 : Entails.eval a c441 := derived441 a h
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c442 := derived442 a h
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c444 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨23, by decide⟩, true), (⟨13, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f444 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c433, some c431, some c122, some c14, some c75, some c391, some c298, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p444 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked444 : lratChecker f444 p444 = .success := by decide +kernel
theorem unsat444 : Unsatisfiable (PosFin 31) f444 := by
  apply lratCheckerSound f444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p444
  · intro a ha; simp [p444] at ha; subst a; trivial
  · exact checked444
theorem derived444 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c444 := by
  apply localUnsat_implies_entails f444 [c407, c433, c431, c122, c14, c75, c391, c298] c444 unsat444 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c431 := derived431 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c391 := derived391 a h
  have h7 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c445 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨23, by decide⟩, true), (⟨13, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f445 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c35, some c36, some c27, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p445 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked445 : lratChecker f445 p445 = .success := by decide +kernel
theorem unsat445 : Unsatisfiable (PosFin 31) f445 := by
  apply lratCheckerSound f445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p445
  · intro a ha; simp [p445] at ha; subst a; trivial
  · exact checked445
theorem derived445 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c445 := by
  apply localUnsat_implies_entails f445 [c35, c36, c27] c445 unsat445 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c446 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨23, by decide⟩, true), (⟨13, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f446 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c34, some c27, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p446 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked446 : lratChecker f446 p446 = .success := by decide +kernel
theorem unsat446 : Unsatisfiable (PosFin 31) f446 := by
  apply lratCheckerSound f446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p446
  · intro a ha; simp [p446] at ha; subst a; trivial
  · exact checked446
theorem derived446 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c446 := by
  apply localUnsat_implies_entails f446 [c33, c34, c27] c446 unsat446 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c447 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f447 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c433, some c431, some c440, some c387, some c445, some c446, some c444, some c14, some c73, some c391, some c298, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p447 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked447 : lratChecker f447 p447 = .success := by decide +kernel
theorem unsat447 : Unsatisfiable (PosFin 31) f447 := by
  apply lratCheckerSound f447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p447
  · intro a ha; simp [p447] at ha; subst a; trivial
  · exact checked447
theorem derived447 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c447 := by
  apply localUnsat_implies_entails f447 [c407, c433, c431, c440, c387, c445, c446, c444, c14, c73, c391, c298] c447 unsat447 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c431 := derived431 a h
  have h3 : Entails.eval a c440 := derived440 a h
  have h4 : Entails.eval a c387 := derived387 a h
  have h5 : Entails.eval a c445 := derived445 a h
  have h6 : Entails.eval a c446 := derived446 a h
  have h7 : Entails.eval a c444 := derived444 a h
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c391 := derived391 a h
  have h11 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c448 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f448 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c433, some c431, some c156, some c232, some c244, some c256, some c5, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p448 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked448 : lratChecker f448 p448 = .success := by decide +kernel
theorem unsat448 : Unsatisfiable (PosFin 31) f448 := by
  apply lratCheckerSound f448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p448
  · intro a ha; simp [p448] at ha; subst a; trivial
  · exact checked448
theorem derived448 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c448 := by
  apply localUnsat_implies_entails f448 [c407, c433, c431, c156, c232, c244, c256, c5] c448 unsat448 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c431 := derived431 a h
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c232 := h 231 (by decide)
  have h5 : Entails.eval a c244 := h 243 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c449 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f449 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c447, some c443, some c433, some c448, some c25, some c158, some c437, some c177, some c65, some c101, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p449 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked449 : lratChecker f449 p449 = .success := by decide +kernel
theorem unsat449 : Unsatisfiable (PosFin 31) f449 := by
  apply lratCheckerSound f449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p449
  · intro a ha; simp [p449] at ha; subst a; trivial
  · exact checked449
theorem derived449 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c449 := by
  apply localUnsat_implies_entails f449 [c407, c447, c443, c433, c448, c25, c158, c437, c177, c65, c101] c449 unsat449 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c447 := derived447 a h
  have h2 : Entails.eval a c443 := derived443 a h
  have h3 : Entails.eval a c433 := derived433 a h
  have h4 : Entails.eval a c448 := derived448 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c158 := h 157 (by decide)
  have h7 : Entails.eval a c437 := derived437 a h
  have h8 : Entails.eval a c177 := h 176 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c450 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f450 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c443, some c447, some c449, some c55, some c51, some c25, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p450 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked450 : lratChecker f450 p450 = .success := by decide +kernel
theorem unsat450 : Unsatisfiable (PosFin 31) f450 := by
  apply lratCheckerSound f450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p450
  · intro a ha; simp [p450] at ha; subst a; trivial
  · exact checked450
theorem derived450 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c450 := by
  apply localUnsat_implies_entails f450 [c443, c447, c449, c55, c51, c25] c450 unsat450 (by rfl) a
  have h0 : Entails.eval a c443 := derived443 a h
  have h1 : Entails.eval a c447 := derived447 a h
  have h2 : Entails.eval a c449 := derived449 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c451 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f451 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c450, some c55, some c51, some c218, some c215, some c3, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p451 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked451 : lratChecker f451 p451 = .success := by decide +kernel
theorem unsat451 : Unsatisfiable (PosFin 31) f451 := by
  apply lratCheckerSound f451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p451
  · intro a ha; simp [p451] at ha; subst a; trivial
  · exact checked451
theorem derived451 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c451 := by
  apply localUnsat_implies_entails f451 [c450, c55, c51, c218, c215, c3] c451 unsat451 (by rfl) a
  have h0 : Entails.eval a c450 := derived450 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c218 := h 217 (by decide)
  have h4 : Entails.eval a c215 := h 214 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c452 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f452 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c451, some c448, some c433, some c387, some c450, some c431, some c25, some c434, some c346, some c305, some c179, some c298, some c3, some c1, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p452 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked452 : lratChecker f452 p452 = .success := by decide +kernel
theorem unsat452 : Unsatisfiable (PosFin 31) f452 := by
  apply lratCheckerSound f452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p452
  · intro a ha; simp [p452] at ha; subst a; trivial
  · exact checked452
theorem derived452 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c452 := by
  apply localUnsat_implies_entails f452 [c407, c451, c448, c433, c387, c450, c431, c25, c434, c346, c305, c179, c298, c3, c1] c452 unsat452 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c451 := derived451 a h
  have h2 : Entails.eval a c448 := derived448 a h
  have h3 : Entails.eval a c433 := derived433 a h
  have h4 : Entails.eval a c387 := derived387 a h
  have h5 : Entails.eval a c450 := derived450 a h
  have h6 : Entails.eval a c431 := derived431 a h
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c434 := derived434 a h
  have h9 : Entails.eval a c346 := derived346 a h
  have h10 : Entails.eval a c305 := h 304 (by decide)
  have h11 : Entails.eval a c179 := h 178 (by decide)
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c453 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f453 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c158, some c437, some c426, some c168, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p453 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked453 : lratChecker f453 p453 = .success := by decide +kernel
theorem unsat453 : Unsatisfiable (PosFin 31) f453 := by
  apply lratCheckerSound f453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p453
  · intro a ha; simp [p453] at ha; subst a; trivial
  · exact checked453
theorem derived453 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c453 := by
  apply localUnsat_implies_entails f453 [c407, c158, c437, c426, c168] c453 unsat453 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c426 := derived426 a h
  have h4 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c454 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f454 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c433, some c431, some c450, some c451, some c387, some c448, some c453, some c452, some c445, some c446, some c444, some c73, some c121, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p454 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked454 : lratChecker f454 p454 = .success := by decide +kernel
theorem unsat454 : Unsatisfiable (PosFin 31) f454 := by
  apply lratCheckerSound f454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p454
  · intro a ha; simp [p454] at ha; subst a; trivial
  · exact checked454
theorem derived454 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c454 := by
  apply localUnsat_implies_entails f454 [c407, c433, c431, c450, c451, c387, c448, c453, c452, c445, c446, c444, c73, c121] c454 unsat454 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c431 := derived431 a h
  have h3 : Entails.eval a c450 := derived450 a h
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c387 := derived387 a h
  have h6 : Entails.eval a c448 := derived448 a h
  have h7 : Entails.eval a c453 := derived453 a h
  have h8 : Entails.eval a c452 := derived452 a h
  have h9 : Entails.eval a c445 := derived445 a h
  have h10 : Entails.eval a c446 := derived446 a h
  have h11 : Entails.eval a c444 := derived444 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c455 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f455 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c433, some c445, some c446, some c121, some c156, some c232, some c152, some c5, some c228, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p455 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked455 : lratChecker f455 p455 = .success := by decide +kernel
theorem unsat455 : Unsatisfiable (PosFin 31) f455 := by
  apply lratCheckerSound f455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p455
  · intro a ha; simp [p455] at ha; subst a; trivial
  · exact checked455
theorem derived455 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c455 := by
  apply localUnsat_implies_entails f455 [c407, c433, c445, c446, c121, c156, c232, c152, c5, c228] c455 unsat455 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c445 := derived445 a h
  have h3 : Entails.eval a c446 := derived446 a h
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c456 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f456 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c454, some c455, some c51, some c142, some c215, some c88, some c307, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p456 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked456 : lratChecker f456 p456 = .success := by decide +kernel
theorem unsat456 : Unsatisfiable (PosFin 31) f456 := by
  apply lratCheckerSound f456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p456
  · intro a ha; simp [p456] at ha; subst a; trivial
  · exact checked456
theorem derived456 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c456 := by
  apply localUnsat_implies_entails f456 [c407, c454, c455, c51, c142, c215, c88, c307] c456 unsat456 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c454 := derived454 a h
  have h2 : Entails.eval a c455 := derived455 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c215 := h 214 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c457 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨29, by decide⟩, false), (⟨13, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f457 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c454, some c431, some c142, some c102, some c75, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p457 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked457 : lratChecker f457 p457 = .success := by decide +kernel
theorem unsat457 : Unsatisfiable (PosFin 31) f457 := by
  apply lratCheckerSound f457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p457
  · intro a ha; simp [p457] at ha; subst a; trivial
  · exact checked457
theorem derived457 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c457 := by
  apply localUnsat_implies_entails f457 [c454, c431, c142, c102, c75] c457 unsat457 (by rfl) a
  have h0 : Entails.eval a c454 := derived454 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c458 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f458 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c433, some c431, some c456, some c457, some c445, some c446, some c73, some c75, some c122, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p458 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked458 : lratChecker f458 p458 = .success := by decide +kernel
theorem unsat458 : Unsatisfiable (PosFin 31) f458 := by
  apply lratCheckerSound f458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p458
  · intro a ha; simp [p458] at ha; subst a; trivial
  · exact checked458
theorem derived458 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c458 := by
  apply localUnsat_implies_entails f458 [c433, c431, c456, c457, c445, c446, c73, c75, c122] c458 unsat458 (by rfl) a
  have h0 : Entails.eval a c433 := derived433 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c456 := derived456 a h
  have h3 : Entails.eval a c457 := derived457 a h
  have h4 : Entails.eval a c445 := derived445 a h
  have h5 : Entails.eval a c446 := derived446 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c459 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f459 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c458, some c25, some c69, some c156, some c426, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p459 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked459 : lratChecker f459 p459 = .success := by decide +kernel
theorem unsat459 : Unsatisfiable (PosFin 31) f459 := by
  apply lratCheckerSound f459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p459
  · intro a ha; simp [p459] at ha; subst a; trivial
  · exact checked459
theorem derived459 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c459 := by
  apply localUnsat_implies_entails f459 [c407, c458, c25, c69, c156, c426] c459 unsat459 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c458 := derived458 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c426 := derived426 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c460 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f460 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c458, some c459, some c434, some c156, some c126, some c426, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p460 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked460 : lratChecker f460 p460 = .success := by decide +kernel
theorem unsat460 : Unsatisfiable (PosFin 31) f460 := by
  apply lratCheckerSound f460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p460
  · intro a ha; simp [p460] at ha; subst a; trivial
  · exact checked460
theorem derived460 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c460 := by
  apply localUnsat_implies_entails f460 [c407, c458, c459, c434, c156, c126, c426] c460 unsat460 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c458 := derived458 a h
  have h2 : Entails.eval a c459 := derived459 a h
  have h3 : Entails.eval a c434 := derived434 a h
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c426 := derived426 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c461 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f461 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c366, some c21, some c179, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p461 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked461 : lratChecker f461 p461 = .success := by decide +kernel
theorem unsat461 : Unsatisfiable (PosFin 31) f461 := by
  apply lratCheckerSound f461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p461
  · intro a ha; simp [p461] at ha; subst a; trivial
  · exact checked461
theorem derived461 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c461 := by
  apply localUnsat_implies_entails f461 [c407, c366, c21, c179] c461 unsat461 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c366 := derived366 a h
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c462 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨20, by decide⟩, true), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f462 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c461, some c19, some c368, some c20, some c179, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p462 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked462 : lratChecker f462 p462 = .success := by decide +kernel
theorem unsat462 : Unsatisfiable (PosFin 31) f462 := by
  apply lratCheckerSound f462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p462
  · intro a ha; simp [p462] at ha; subst a; trivial
  · exact checked462
theorem derived462 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c462 := by
  apply localUnsat_implies_entails f462 [c407, c461, c19, c368, c20, c179] c462 unsat462 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c461 := derived461 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c368 := derived368 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c463 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f463 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c460, some c462, some c156, some c232, some c51, some c16, some c314, some c20, some c304, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p463 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked463 : lratChecker f463 p463 = .success := by decide +kernel
theorem unsat463 : Unsatisfiable (PosFin 31) f463 := by
  apply lratCheckerSound f463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p463
  · intro a ha; simp [p463] at ha; subst a; trivial
  · exact checked463
theorem derived463 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c463 := by
  apply localUnsat_implies_entails f463 [c407, c460, c462, c156, c232, c51, c16, c314, c20, c304] c463 unsat463 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c460 := derived460 a h
  have h2 : Entails.eval a c462 := derived462 a h
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c232 := h 231 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c464 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f464 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c458, some c460, some c463, some c25, some c156, some c232, some c152, some c317, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p464 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked464 : lratChecker f464 p464 = .success := by decide +kernel
theorem unsat464 : Unsatisfiable (PosFin 31) f464 := by
  apply lratCheckerSound f464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p464
  · intro a ha; simp [p464] at ha; subst a; trivial
  · exact checked464
theorem derived464 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c464 := by
  apply localUnsat_implies_entails f464 [c407, c458, c460, c463, c25, c156, c232, c152, c317] c464 unsat464 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c458 := derived458 a h
  have h2 : Entails.eval a c460 := derived460 a h
  have h3 : Entails.eval a c463 := derived463 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c465 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f465 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c8, some c464, some c454, some c455, some c316, some c13, some c308, some c2, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p465 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked465 : lratChecker f465 p465 = .success := by decide +kernel
theorem unsat465 : Unsatisfiable (PosFin 31) f465 := by
  apply lratCheckerSound f465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p465
  · intro a ha; simp [p465] at ha; subst a; trivial
  · exact checked465
theorem derived465 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c465 := by
  apply localUnsat_implies_entails f465 [c407, c8, c464, c454, c455, c316, c13, c308, c2] c465 unsat465 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c464 := derived464 a h
  have h3 : Entails.eval a c454 := derived454 a h
  have h4 : Entails.eval a c455 := derived455 a h
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c308 := h 307 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c466 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f466 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c454, some c142, some c440, some c88, some c13, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p466 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked466 : lratChecker f466 p466 = .success := by decide +kernel
theorem unsat466 : Unsatisfiable (PosFin 31) f466 := by
  apply lratCheckerSound f466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p466
  · intro a ha; simp [p466] at ha; subst a; trivial
  · exact checked466
theorem derived466 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c466 := by
  apply localUnsat_implies_entails f466 [c454, c142, c440, c88, c13] c466 unsat466 (by rfl) a
  have h0 : Entails.eval a c454 := derived454 a h
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c440 := derived440 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c467 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f467 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c464, some c466, some c454, some c433, some c455, some c465, some c13, some c308, some c253, some c346, some c292, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p467 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked467 : lratChecker f467 p467 = .success := by decide +kernel
theorem unsat467 : Unsatisfiable (PosFin 31) f467 := by
  apply lratCheckerSound f467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p467
  · intro a ha; simp [p467] at ha; subst a; trivial
  · exact checked467
theorem derived467 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c467 := by
  apply localUnsat_implies_entails f467 [c407, c464, c466, c454, c433, c455, c465, c13, c308, c253, c346, c292] c467 unsat467 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c464 := derived464 a h
  have h2 : Entails.eval a c466 := derived466 a h
  have h3 : Entails.eval a c454 := derived454 a h
  have h4 : Entails.eval a c433 := derived433 a h
  have h5 : Entails.eval a c455 := derived455 a h
  have h6 : Entails.eval a c465 := derived465 a h
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c308 := h 307 (by decide)
  have h9 : Entails.eval a c253 := h 252 (by decide)
  have h10 : Entails.eval a c346 := derived346 a h
  have h11 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c468 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f468 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c466, some c454, some c433, some c294, some c296, some c254, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p468 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked468 : lratChecker f468 p468 = .success := by decide +kernel
theorem unsat468 : Unsatisfiable (PosFin 31) f468 := by
  apply lratCheckerSound f468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p468
  · intro a ha; simp [p468] at ha; subst a; trivial
  · exact checked468
theorem derived468 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c468 := by
  apply localUnsat_implies_entails f468 [c466, c454, c433, c294, c296, c254] c468 unsat468 (by rfl) a
  have h0 : Entails.eval a c466 := derived466 a h
  have h1 : Entails.eval a c454 := derived454 a h
  have h2 : Entails.eval a c433 := derived433 a h
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c296 := h 295 (by decide)
  have h5 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c469 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f469 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c467, some c464, some c466, some c433, some c431, some c446, some c73, some c75, some c122, some c445, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p469 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked469 : lratChecker f469 p469 = .success := by decide +kernel
theorem unsat469 : Unsatisfiable (PosFin 31) f469 := by
  apply lratCheckerSound f469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p469
  · intro a ha; simp [p469] at ha; subst a; trivial
  · exact checked469
theorem derived469 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c469 := by
  apply localUnsat_implies_entails f469 [c467, c464, c466, c433, c431, c446, c73, c75, c122, c445] c469 unsat469 (by rfl) a
  have h0 : Entails.eval a c467 := derived467 a h
  have h1 : Entails.eval a c464 := derived464 a h
  have h2 : Entails.eval a c466 := derived466 a h
  have h3 : Entails.eval a c433 := derived433 a h
  have h4 : Entails.eval a c431 := derived431 a h
  have h5 : Entails.eval a c446 := derived446 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c445 := derived445 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c470 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f470 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c454, some c464, some c466, some c467, some c469, some c13, some c434, some c468, some c94, some c316, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p470 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked470 : lratChecker f470 p470 = .success := by decide +kernel
theorem unsat470 : Unsatisfiable (PosFin 31) f470 := by
  apply lratCheckerSound f470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p470
  · intro a ha; simp [p470] at ha; subst a; trivial
  · exact checked470
theorem derived470 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c470 := by
  apply localUnsat_implies_entails f470 [c407, c454, c464, c466, c467, c469, c13, c434, c468, c94, c316] c470 unsat470 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c454 := derived454 a h
  have h2 : Entails.eval a c464 := derived464 a h
  have h3 : Entails.eval a c466 := derived466 a h
  have h4 : Entails.eval a c467 := derived467 a h
  have h5 : Entails.eval a c469 := derived469 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c434 := derived434 a h
  have h8 : Entails.eval a c468 := derived468 a h
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c471 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f471 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c454, some c470, some c158, some c55, some c437, some c453, some c234, some c96, some c316, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p471 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked471 : lratChecker f471 p471 = .success := by decide +kernel
theorem unsat471 : Unsatisfiable (PosFin 31) f471 := by
  apply lratCheckerSound f471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p471
  · intro a ha; simp [p471] at ha; subst a; trivial
  · exact checked471
theorem derived471 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c471 := by
  apply localUnsat_implies_entails f471 [c407, c454, c470, c158, c55, c437, c453, c234, c96, c316] c471 unsat471 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c454 := derived454 a h
  have h2 : Entails.eval a c470 := derived470 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c437 := derived437 a h
  have h6 : Entails.eval a c453 := derived453 a h
  have h7 : Entails.eval a c234 := h 233 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c472 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f472 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c316, some c13, some c29, some c39, some c17, some c76, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p472 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked472 : lratChecker f472 p472 = .success := by decide +kernel
theorem unsat472 : Unsatisfiable (PosFin 31) f472 := by
  apply lratCheckerSound f472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p472
  · intro a ha; simp [p472] at ha; subst a; trivial
  · exact checked472
theorem derived472 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c472 := by
  apply localUnsat_implies_entails f472 [c407, c471, c316, c13, c29, c39, c17, c76] c472 unsat472 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c316 := h 315 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c473 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f473 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c210, some c209, some c76, some c354, some c26, some c138, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p473 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked473 : lratChecker f473 p473 = .success := by decide +kernel
theorem unsat473 : Unsatisfiable (PosFin 31) f473 := by
  apply lratCheckerSound f473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p473
  · intro a ha; simp [p473] at ha; subst a; trivial
  · exact checked473
theorem derived473 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c473 := by
  apply localUnsat_implies_entails f473 [c407, c471, c210, c209, c76, c354, c26, c138] c473 unsat473 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c354 := derived354 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c474 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f474 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c472, some c132, some c130, some c473, some c101, some c213, some c150, some c255, some c389, some c327, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p474 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked474 : lratChecker f474 p474 = .success := by decide +kernel
theorem unsat474 : Unsatisfiable (PosFin 31) f474 := by
  apply lratCheckerSound f474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p474
  · intro a ha; simp [p474] at ha; subst a; trivial
  · exact checked474
theorem derived474 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c474 := by
  apply localUnsat_implies_entails f474 [c472, c132, c130, c473, c101, c213, c150, c255, c389, c327] c474 unsat474 (by rfl) a
  have h0 : Entails.eval a c472 := derived472 a h
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c473 := derived473 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c255 := h 254 (by decide)
  have h8 : Entails.eval a c389 := derived389 a h
  have h9 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c475 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f475 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c407, some c474, some c8, some c293, some c295, some c4, some c153, some c229, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p475 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked475 : lratChecker f475 p475 = .success := by decide +kernel
theorem unsat475 : Unsatisfiable (PosFin 31) f475 := by
  apply lratCheckerSound f475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p475
  · intro a ha; simp [p475] at ha; subst a; trivial
  · exact checked475
theorem derived475 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c475 := by
  apply localUnsat_implies_entails f475 [c471, c407, c474, c8, c293, c295, c4, c153, c229] c475 unsat475 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c474 := derived474 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c476 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f476 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c207, some c208, some c26, some c54, some c5, some c354, some c229, some c300, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p476 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked476 : lratChecker f476 p476 = .success := by decide +kernel
theorem unsat476 : Unsatisfiable (PosFin 31) f476 := by
  apply lratCheckerSound f476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p476
  · intro a ha; simp [p476] at ha; subst a; trivial
  · exact checked476
theorem derived476 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c476 := by
  apply localUnsat_implies_entails f476 [c407, c471, c207, c208, c26, c54, c5, c354, c229, c300] c476 unsat476 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c354 := derived354 a h
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c477 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f477 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c153, some c229, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p477 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked477 : lratChecker f477 p477 = .success := by decide +kernel
theorem unsat477 : Unsatisfiable (PosFin 31) f477 := by
  apply lratCheckerSound f477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p477
  · intro a ha; simp [p477] at ha; subst a; trivial
  · exact checked477
theorem derived477 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c477 := by
  apply localUnsat_implies_entails f477 [c153, c229] c477 unsat477 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c478 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨13, by decide⟩, true), (⟨20, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f478 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c8, some c477, some c100, some c210, some c209, some c26, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p478 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked478 : lratChecker f478 p478 = .success := by decide +kernel
theorem unsat478 : Unsatisfiable (PosFin 31) f478 := by
  apply lratCheckerSound f478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p478
  · intro a ha; simp [p478] at ha; subst a; trivial
  · exact checked478
theorem derived478 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c478 := by
  apply localUnsat_implies_entails f478 [c407, c471, c8, c477, c100, c210, c209, c26] c478 unsat478 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c477 := derived477 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c479 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨21, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f479 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c243, some c284, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p479 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked479 : lratChecker f479 p479 = .success := by decide +kernel
theorem unsat479 : Unsatisfiable (PosFin 31) f479 := by
  apply lratCheckerSound f479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p479
  · intro a ha; simp [p479] at ha; subst a; trivial
  · exact checked479
theorem derived479 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c479 := by
  apply localUnsat_implies_entails f479 [c243, c284] c479 unsat479 (by rfl) a
  have h0 : Entails.eval a c243 := h 242 (by decide)
  have h1 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c480 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨21, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f480 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c407, some c26, some c76, some c479, some c303, some c260, some c196, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p480 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked480 : lratChecker f480 p480 = .success := by decide +kernel
theorem unsat480 : Unsatisfiable (PosFin 31) f480 := by
  apply lratCheckerSound f480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p480
  · intro a ha; simp [p480] at ha; subst a; trivial
  · exact checked480
theorem derived480 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c480 := by
  apply localUnsat_implies_entails f480 [c471, c407, c26, c76, c479, c303, c260, c196] c480 unsat480 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c479 := derived479 a h
  have h5 : Entails.eval a c303 := h 302 (by decide)
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c481 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨21, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f481 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c407, some c480, some c479, some c303, some c288, some c287, some c30, some c32, some c18, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p481 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked481 : lratChecker f481 p481 = .success := by decide +kernel
theorem unsat481 : Unsatisfiable (PosFin 31) f481 := by
  apply lratCheckerSound f481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p481
  · intro a ha; simp [p481] at ha; subst a; trivial
  · exact checked481
theorem derived481 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c481 := by
  apply localUnsat_implies_entails f481 [c471, c407, c480, c479, c303, c288, c287, c30, c32, c18] c481 unsat481 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c480 := derived480 a h
  have h3 : Entails.eval a c479 := derived479 a h
  have h4 : Entails.eval a c303 := h 302 (by decide)
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c287 := h 286 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c482 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f482 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c261, some c197, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p482 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked482 : lratChecker f482 p482 = .success := by decide +kernel
theorem unsat482 : Unsatisfiable (PosFin 31) f482 := by
  apply lratCheckerSound f482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p482
  · intro a ha; simp [p482] at ha; subst a; trivial
  · exact checked482
theorem derived482 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c482 := by
  apply localUnsat_implies_entails f482 [c261, c197] c482 unsat482 (by rfl) a
  have h0 : Entails.eval a c261 := h 260 (by decide)
  have h1 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c483 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f483 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c480, some c481, some c73, some c482, some c303, some c245, some c285, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p483 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked483 : lratChecker f483 p483 = .success := by decide +kernel
theorem unsat483 : Unsatisfiable (PosFin 31) f483 := by
  apply lratCheckerSound f483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p483
  · intro a ha; simp [p483] at ha; subst a; trivial
  · exact checked483
theorem derived483 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c483 := by
  apply localUnsat_implies_entails f483 [c407, c471, c480, c481, c73, c482, c303, c245, c285] c483 unsat483 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c480 := derived480 a h
  have h3 : Entails.eval a c481 := derived481 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c482 := derived482 a h
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c484 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f484 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c483, some c157, some c246, some c258, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p484 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked484 : lratChecker f484 p484 = .success := by decide +kernel
theorem unsat484 : Unsatisfiable (PosFin 31) f484 := by
  apply lratCheckerSound f484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p484
  · intro a ha; simp [p484] at ha; subst a; trivial
  · exact checked484
theorem derived484 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c484 := by
  apply localUnsat_implies_entails f484 [c407, c471, c483, c157, c246, c258] c484 unsat484 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c483 := derived483 a h
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c246 := h 245 (by decide)
  have h5 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c485 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨20, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f485 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c475, some c478, some c484, some c5, some c248, some c54, some c150, some c480, some c93, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p485 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked485 : lratChecker f485 p485 = .success := by decide +kernel
theorem unsat485 : Unsatisfiable (PosFin 31) f485 := by
  apply lratCheckerSound f485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p485
  · intro a ha; simp [p485] at ha; subst a; trivial
  · exact checked485
theorem derived485 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c485 := by
  apply localUnsat_implies_entails f485 [c475, c478, c484, c5, c248, c54, c150, c480, c93] c485 unsat485 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c478 := derived478 a h
  have h2 : Entails.eval a c484 := derived484 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c248 := h 247 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c480 := derived480 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c486 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f486 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c476, some c485, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p486 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked486 : lratChecker f486 p486 = .success := by decide +kernel
theorem unsat486 : Unsatisfiable (PosFin 31) f486 := by
  apply lratCheckerSound f486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p486
  · intro a ha; simp [p486] at ha; subst a; trivial
  · exact checked486
theorem derived486 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c486 := by
  apply localUnsat_implies_entails f486 [c476, c485] c486 unsat486 (by rfl) a
  have h0 : Entails.eval a c476 := derived476 a h
  have h1 : Entails.eval a c485 := derived485 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c487 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f487 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c210, some c209, some c26, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p487 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked487 : lratChecker f487 p487 = .success := by decide +kernel
theorem unsat487 : Unsatisfiable (PosFin 31) f487 := by
  apply lratCheckerSound f487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p487
  · intro a ha; simp [p487] at ha; subst a; trivial
  · exact checked487
theorem derived487 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c487 := by
  apply localUnsat_implies_entails f487 [c407, c471, c210, c209, c26] c487 unsat487 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c488 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f488 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c486, some c487, some c100, some c25, some c69, some c71, some c101, some c148, some c389, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p488 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked488 : lratChecker f488 p488 = .success := by decide +kernel
theorem unsat488 : Unsatisfiable (PosFin 31) f488 := by
  apply lratCheckerSound f488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p488
  · intro a ha; simp [p488] at ha; subst a; trivial
  · exact checked488
theorem derived488 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c488 := by
  apply localUnsat_implies_entails f488 [c407, c471, c486, c487, c100, c25, c69, c71, c101, c148, c389] c488 unsat488 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c486 := derived486 a h
  have h3 : Entails.eval a c487 := derived487 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c389 := derived389 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c489 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f489 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c25, some c69, some c71, some c50, some c101, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p489 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked489 : lratChecker f489 p489 = .success := by decide +kernel
theorem unsat489 : Unsatisfiable (PosFin 31) f489 := by
  apply lratCheckerSound f489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p489
  · intro a ha; simp [p489] at ha; subst a; trivial
  · exact checked489
theorem derived489 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c489 := by
  apply localUnsat_implies_entails f489 [c25, c69, c71, c50, c101] c489 unsat489 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c490 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f490 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c488, some c486, some c489, some c210, some c209, some c434, some c354, some c50, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p490 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked490 : lratChecker f490 p490 = .success := by decide +kernel
theorem unsat490 : Unsatisfiable (PosFin 31) f490 := by
  apply lratCheckerSound f490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p490
  · intro a ha; simp [p490] at ha; subst a; trivial
  · exact checked490
theorem derived490 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c490 := by
  apply localUnsat_implies_entails f490 [c407, c471, c488, c486, c489, c210, c209, c434, c354, c50] c490 unsat490 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c488 := derived488 a h
  have h3 : Entails.eval a c486 := derived486 a h
  have h4 : Entails.eval a c489 := derived489 a h
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c434 := derived434 a h
  have h8 : Entails.eval a c354 := derived354 a h
  have h9 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c491 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f491 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c151, some c227, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p491 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked491 : lratChecker f491 p491 = .success := by decide +kernel
theorem unsat491 : Unsatisfiable (PosFin 31) f491 := by
  apply lratCheckerSound f491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p491
  · intro a ha; simp [p491] at ha; subst a; trivial
  · exact checked491
theorem derived491 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c491 := by
  apply localUnsat_implies_entails f491 [c151, c227] c491 unsat491 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c492 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f492 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c486, some c488, some c490, some c8, some c491, some c25, some c210, some c209, some c121, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p492 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked492 : lratChecker f492 p492 = .success := by decide +kernel
theorem unsat492 : Unsatisfiable (PosFin 31) f492 := by
  apply lratCheckerSound f492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p492
  · intro a ha; simp [p492] at ha; subst a; trivial
  · exact checked492
theorem derived492 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c492 := by
  apply localUnsat_implies_entails f492 [c407, c486, c488, c490, c8, c491, c25, c210, c209, c121] c492 unsat492 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c486 := derived486 a h
  have h2 : Entails.eval a c488 := derived488 a h
  have h3 : Entails.eval a c490 := derived490 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c491 := derived491 a h
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c493 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f493 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c407, some c492, some c207, some c208, some c26, some c486, some c8, some c121, some c491, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p493 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked493 : lratChecker f493 p493 = .success := by decide +kernel
theorem unsat493 : Unsatisfiable (PosFin 31) f493 := by
  apply lratCheckerSound f493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p493
  · intro a ha; simp [p493] at ha; subst a; trivial
  · exact checked493
theorem derived493 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c493 := by
  apply localUnsat_implies_entails f493 [c471, c407, c492, c207, c208, c26, c486, c8, c121, c491] c493 unsat493 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c492 := derived492 a h
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c486 := derived486 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c491 := derived491 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c494 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f494 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c407, some c486, some c492, some c207, some c208, some c26, some c493, some c76, some c78, some c354, some c138, some c141, some c217, some c214, some c50, some c3, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p494 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked494 : lratChecker f494 p494 = .success := by decide +kernel
theorem unsat494 : Unsatisfiable (PosFin 31) f494 := by
  apply lratCheckerSound f494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p494
  · intro a ha; simp [p494] at ha; subst a; trivial
  · exact checked494
theorem derived494 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c494 := by
  apply localUnsat_implies_entails f494 [c471, c407, c486, c492, c207, c208, c26, c493, c76, c78, c354, c138, c141, c217, c214, c50, c3] c494 unsat494 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c486 := derived486 a h
  have h3 : Entails.eval a c492 := derived492 a h
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c493 := derived493 a h
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c354 := derived354 a h
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c214 := h 213 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c495 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f495 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c49, some c53, some c45, some c411, some c386, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p495 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked495 : lratChecker f495 p495 = .success := by decide +kernel
theorem unsat495 : Unsatisfiable (PosFin 31) f495 := by
  apply lratCheckerSound f495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p495
  · intro a ha; simp [p495] at ha; subst a; trivial
  · exact checked495
theorem derived495 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c495 := by
  apply localUnsat_implies_entails f495 [c49, c53, c45, c411, c386] c495 unsat495 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c411 := derived411 a h
  have h4 : Entails.eval a c386 := derived386 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c496 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f496 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c494, some c49, some c53, some c207, some c209, some c25, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p496 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked496 : lratChecker f496 p496 = .success := by decide +kernel
theorem unsat496 : Unsatisfiable (PosFin 31) f496 := by
  apply lratCheckerSound f496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p496
  · intro a ha; simp [p496] at ha; subst a; trivial
  · exact checked496
theorem derived496 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c496 := by
  apply localUnsat_implies_entails f496 [c407, c494, c49, c53, c207, c209, c25] c496 unsat496 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c494 := derived494 a h
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c497 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f497 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c494, some c53, some c49, some c495, some c496, some c121, some c208, some c210, some c25, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p497 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked497 : lratChecker f497 p497 = .success := by decide +kernel
theorem unsat497 : Unsatisfiable (PosFin 31) f497 := by
  apply lratCheckerSound f497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p497
  · intro a ha; simp [p497] at ha; subst a; trivial
  · exact checked497
theorem derived497 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c497 := by
  apply localUnsat_implies_entails f497 [c407, c494, c53, c49, c495, c496, c121, c208, c210, c25] c497 unsat497 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c494 := derived494 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c495 := derived495 a h
  have h5 : Entails.eval a c496 := derived496 a h
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c498 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f498 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c497, some c207, some c208, some c26, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p498 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked498 : lratChecker f498 p498 = .success := by decide +kernel
theorem unsat498 : Unsatisfiable (PosFin 31) f498 := by
  apply lratCheckerSound f498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p498
  · intro a ha; simp [p498] at ha; subst a; trivial
  · exact checked498
theorem derived498 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c498 := by
  apply localUnsat_implies_entails f498 [c407, c471, c497, c207, c208, c26] c498 unsat498 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c499 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f499 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c497, some c494, some c487, some c498, some c315, some c303, some c100, some c26, some c480, some c78, some c13, some c326, some c263, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p499 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked499 : lratChecker f499 p499 = .success := by decide +kernel
theorem unsat499 : Unsatisfiable (PosFin 31) f499 := by
  apply lratCheckerSound f499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p499
  · intro a ha; simp [p499] at ha; subst a; trivial
  · exact checked499
theorem derived499 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c499 := by
  apply localUnsat_implies_entails f499 [c407, c471, c497, c494, c487, c498, c315, c303, c100, c26, c480, c78, c13, c326, c263] c499 unsat499 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c494 := derived494 a h
  have h4 : Entails.eval a c487 := derived487 a h
  have h5 : Entails.eval a c498 := derived498 a h
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c480 := derived480 a h
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c326 := h 325 (by decide)
  have h14 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c500 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f500 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c494, some c497, some c487, some c498, some c100, some c315, some c303, some c499, some c32, some c350, some c344, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p500 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked500 : lratChecker f500 p500 = .success := by decide +kernel
theorem unsat500 : Unsatisfiable (PosFin 31) f500 := by
  apply lratCheckerSound f500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p500
  · intro a ha; simp [p500] at ha; subst a; trivial
  · exact checked500
theorem derived500 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c500 := by
  apply localUnsat_implies_entails f500 [c407, c471, c494, c497, c487, c498, c100, c315, c303, c499, c32, c350, c344] c500 unsat500 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c494 := derived494 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c487 := derived487 a h
  have h5 : Entails.eval a c498 := derived498 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c499 := derived499 a h
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c350 := derived350 a h
  have h12 : Entails.eval a c344 := derived344 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c501 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f501 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c500, some c471, some c294, some c296, some c4, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p501 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked501 : lratChecker f501 p501 = .success := by decide +kernel
theorem unsat501 : Unsatisfiable (PosFin 31) f501 := by
  apply lratCheckerSound f501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p501
  · intro a ha; simp [p501] at ha; subst a; trivial
  · exact checked501
theorem derived501 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c501 := by
  apply localUnsat_implies_entails f501 [c500, c471, c294, c296, c4] c501 unsat501 (by rfl) a
  have h0 : Entails.eval a c500 := derived500 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c294 := h 293 (by decide)
  have h3 : Entails.eval a c296 := h 295 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c502 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f502 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c479, some c4, some c246, some c192, some c193, some c183, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p502 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked502 : lratChecker f502 p502 = .success := by decide +kernel
theorem unsat502 : Unsatisfiable (PosFin 31) f502 := by
  apply lratCheckerSound f502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p502
  · intro a ha; simp [p502] at ha; subst a; trivial
  · exact checked502
theorem derived502 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c502 := by
  apply localUnsat_implies_entails f502 [c471, c479, c4, c246, c192, c193, c183] c502 unsat502 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c479 := derived479 a h
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c246 := h 245 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c503 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f503 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c479, some c502, some c194, some c195, some c286, some c183, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p503 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked503 : lratChecker f503 p503 = .success := by decide +kernel
theorem unsat503 : Unsatisfiable (PosFin 31) f503 := by
  apply lratCheckerSound f503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p503
  · intro a ha; simp [p503] at ha; subst a; trivial
  · exact checked503
theorem derived503 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c503 := by
  apply localUnsat_implies_entails f503 [c471, c479, c502, c194, c195, c286, c183] c503 unsat503 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c479 := derived479 a h
  have h2 : Entails.eval a c502 := derived502 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c195 := h 194 (by decide)
  have h5 : Entails.eval a c286 := h 285 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c504 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f504 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c503, some c501, some c36, some c33, some c194, some c195, some c125, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p504 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked504 : lratChecker f504 p504 = .success := by decide +kernel
theorem unsat504 : Unsatisfiable (PosFin 31) f504 := by
  apply lratCheckerSound f504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p504
  · intro a ha; simp [p504] at ha; subst a; trivial
  · exact checked504
theorem derived504 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c504 := by
  apply localUnsat_implies_entails f504 [c471, c503, c501, c36, c33, c194, c195, c125] c504 unsat504 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c503 := derived503 a h
  have h2 : Entails.eval a c501 := derived501 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c505 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c500, some c503, some c501, some c33, some c36, some c273, some c15, some c504, some c4, some c247, some c192, some c193, some c17, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p505 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 31) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c471, c500, c503, c501, c33, c36, c273, c15, c504, c4, c247, c192, c193, c17] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c500 := derived500 a h
  have h2 : Entails.eval a c503 := derived503 a h
  have h3 : Entails.eval a c501 := derived501 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c504 := derived504 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c193 := h 192 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c500, some c11, some c9, some c6, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p506 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 31) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c500, c11, c9, c6] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c500 := derived500 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c500, some c471, some c73, some c75, some c506, some c4, some c10, some c12, some c6, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p507 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 31) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c500, c471, c73, c75, c506, c4, c10, c12, c6] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c500 := derived500 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c506 := derived506 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c500, some c471, some c505, some c76, some c78, some c506, some c4, some c10, some c12, some c6, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p508 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 31) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c500, c471, c505, c76, c78, c506, c4, c10, c12, c6] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c500 := derived500 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c505 := derived505 a h
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c506 := derived506 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c507, some c508, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p509 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 31) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c507, c508] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c507 := derived507 a h
  have h1 : Entails.eval a c508 := derived508 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c510 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c471, some c500, some c407, some c509, some c100, some c501, some c274, some c479, some c19, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p510 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 31) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c471, c500, c407, c509, c100, c501, c274, c479, c19] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c500 := derived500 a h
  have h2 : Entails.eval a c407 := derived407 a h
  have h3 : Entails.eval a c509 := derived509 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c501 := derived501 a h
  have h6 : Entails.eval a c274 := h 273 (by decide)
  have h7 : Entails.eval a c479 := derived479 a h
  have h8 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨15, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c500, some c203, some c272, some c268, some c19, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p511 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 31) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c407, c500, c203, c272, c268, c19] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c500 := derived500 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c509, some c510, some c511, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p512 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 31) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c509, c510, c511] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c509 := derived509 a h
  have h1 : Entails.eval a c510 := derived510 a h
  have h2 : Entails.eval a c511 := derived511 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c500, some c204, some c273, some c269, some c19, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p513 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 31) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c407, c500, c204, c273, c269, c19] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c500 := derived500 a h
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c514 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f514 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c500, some c206, some c275, some c271, some c19, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p514 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked514 : lratChecker f514 p514 = .success := by decide +kernel
theorem unsat514 : Unsatisfiable (PosFin 31) f514 := by
  apply lratCheckerSound f514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p514
  · intro a ha; simp [p514] at ha; subst a; trivial
  · exact checked514
theorem derived514 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c514 := by
  apply localUnsat_implies_entails f514 [c407, c500, c206, c275, c271, c19] c514 unsat514 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c500 := derived500 a h
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c271 := h 270 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c515 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f515 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c471, some c509, some c512, some c26, some c513, some c100, some c514, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p515 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked515 : lratChecker f515 p515 = .success := by decide +kernel
theorem unsat515 : Unsatisfiable (PosFin 31) f515 := by
  apply lratCheckerSound f515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p515
  · intro a ha; simp [p515] at ha; subst a; trivial
  · exact checked515
theorem derived515 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c515 := by
  apply localUnsat_implies_entails f515 [c407, c471, c509, c512, c26, c513, c100, c514] c515 unsat515 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c509 := derived509 a h
  have h3 : Entails.eval a c512 := derived512 a h
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c513 := derived513 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c514 := derived514 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c516 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f516 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c515, some c151, some c153, some c513, some c514, some c25, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p516 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked516 : lratChecker f516 p516 = .success := by decide +kernel
theorem unsat516 : Unsatisfiable (PosFin 31) f516 := by
  apply lratCheckerSound f516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p516
  · intro a ha; simp [p516] at ha; subst a; trivial
  · exact checked516
theorem derived516 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c516 := by
  apply localUnsat_implies_entails f516 [c515, c151, c153, c513, c514, c25] c516 unsat516 (by rfl) a
  have h0 : Entails.eval a c515 := derived515 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c514 := derived514 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c517 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f517 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c500, some c407, some c515, some c153, some c19, some c151, some c516, some c121, some c511, some c274, some c25, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p517 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked517 : lratChecker f517 p517 = .success := by decide +kernel
theorem unsat517 : Unsatisfiable (PosFin 31) f517 := by
  apply lratCheckerSound f517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p517
  · intro a ha; simp [p517] at ha; subst a; trivial
  · exact checked517
theorem derived517 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c517 := by
  apply localUnsat_implies_entails f517 [c500, c407, c515, c153, c19, c151, c516, c121, c511, c274, c25] c517 unsat517 (by rfl) a
  have h0 : Entails.eval a c500 := derived500 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c515 := derived515 a h
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c516 := derived516 a h
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c511 := derived511 a h
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c518 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f518 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c407, some c500, some c515, some c155, some c231, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p518 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked518 : lratChecker f518 p518 = .success := by decide +kernel
theorem unsat518 : Unsatisfiable (PosFin 31) f518 := by
  apply lratCheckerSound f518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p518
  · intro a ha; simp [p518] at ha; subst a; trivial
  · exact checked518
theorem derived518 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c518 := by
  apply localUnsat_implies_entails f518 [c407, c500, c515, c155, c231] c518 unsat518 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c500 := derived500 a h
  have h2 : Entails.eval a c515 := derived515 a h
  have h3 : Entails.eval a c155 := h 154 (by decide)
  have h4 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c519 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c500, some c515, some c407, some c233, some c157, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p519 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 31) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c500, c515, c407, c233, c157] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c500 := derived500 a h
  have h1 : Entails.eval a c515 := derived515 a h
  have h2 : Entails.eval a c407 := derived407 a h
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c518, some c519, some c517, some c511, some c25, some c205, some c270, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p520 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 31) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c518, c519, c517, c511, c25, c205, c270] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c517 := derived517 a h
  have h3 : Entails.eval a c511 := derived511 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c519, some c518, some c513, some c514, some c25, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p521 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 31) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c519, c518, c513, c514, c25] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c519 := derived519 a h
  have h1 : Entails.eval a c518 := derived518 a h
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c514 := derived514 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c522 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c518, some c519, some c407, some c121, some c521, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p522 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 31) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c518, c519, c407, c121, c521] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c407 := derived407 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c521 := derived521 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c523 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c520, some c522, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p523 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 31) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c520, c522] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c520 := derived520 a h
  have h1 : Entails.eval a c522 := derived522 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c524 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c518, some c519, some c523, some c411, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p524 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 31) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c518, c519, c523, c411] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c519 := derived519 a h
  have h2 : Entails.eval a c523 := derived523 a h
  have h3 : Entails.eval a c411 := derived411 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c525 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c518, some c523, some c524, some c519, some c370, some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p525 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 31) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c518, c523, c524, c519, c370] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c518 := derived518 a h
  have h1 : Entails.eval a c523 := derived523 a h
  have h2 : Entails.eval a c524 := derived524 a h
  have h3 : Entails.eval a c519 := derived519 a h
  have h4 : Entails.eval a c370 := derived370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c519, some c525, some c523, some c69, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p526 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 31) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c519, c525, c523, c69] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c519 := derived519 a h
  have h1 : Entails.eval a c525 := derived525 a h
  have h2 : Entails.eval a c523 := derived523 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c526, some c524, some c518, some c519, some c386]
def p527 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 31) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c526, c524, c518, c519, c386] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c526 := derived526 a h
  have h1 : Entails.eval a c524 := derived524 a h
  have h2 : Entails.eval a c518 := derived518 a h
  have h3 : Entails.eval a c519 := derived519 a h
  have h4 : Entails.eval a c386 := derived386 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived527

end CochromaticTwenty.Certificates.Z12Direct_5_8_10
