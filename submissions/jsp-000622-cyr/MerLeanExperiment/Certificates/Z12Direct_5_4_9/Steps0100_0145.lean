import MerLeanExperiment.Certificates.Z12Direct_5_4_9.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_4_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c362 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f362 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c41, some c361, some c131, some c165, some c152, some c40, some c230, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p362 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked362 : lratChecker f362 p362 = .success := by decide +kernel
theorem unsat362 : Unsatisfiable (PosFin 31) f362 := by
  apply lratCheckerSound f362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p362
  · intro a ha; simp [p362] at ha; subst a; trivial
  · exact checked362
theorem derived362 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c362 := by
  apply localUnsat_implies_entails f362 [c349, c41, c361, c131, c165, c152, c40, c230] c362 unsat362 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c361 := derived361 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c363 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f363 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c247, some c231, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p363 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked363 : lratChecker f363 p363 = .success := by decide +kernel
theorem unsat363 : Unsatisfiable (PosFin 31) f363 := by
  apply lratCheckerSound f363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p363
  · intro a ha; simp [p363] at ha; subst a; trivial
  · exact checked363
theorem derived363 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c363 := by
  apply localUnsat_implies_entails f363 [c349, c247, c231] c363 unsat363 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c247 := h 246 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c364 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f364 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c151, some c178, some c363, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p364 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked364 : lratChecker f364 p364 = .success := by decide +kernel
theorem unsat364 : Unsatisfiable (PosFin 31) f364 := by
  apply lratCheckerSound f364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p364
  · intro a ha; simp [p364] at ha; subst a; trivial
  · exact checked364
theorem derived364 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c364 := by
  apply localUnsat_implies_entails f364 [c349, c151, c178, c363] c364 unsat364 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c363 := derived363 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c365 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f365 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c350, some c362, some c359, some c364, some c129, some c36, some c20, some c2, some c79, some c65, some c22, some c54, some c134, some c18, some c105, some c117, some c238, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p365 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked365 : lratChecker f365 p365 = .success := by decide +kernel
theorem unsat365 : Unsatisfiable (PosFin 31) f365 := by
  apply lratCheckerSound f365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p365
  · intro a ha; simp [p365] at ha; subst a; trivial
  · exact checked365
theorem derived365 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c365 := by
  apply localUnsat_implies_entails f365 [c349, c350, c362, c359, c364, c129, c36, c20, c2, c79, c65, c22, c54, c134, c18, c105, c117, c238] c365 unsat365 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c362 := derived362 a h
  have h3 : Entails.eval a c359 := derived359 a h
  have h4 : Entails.eval a c364 := derived364 a h
  have h5 : Entails.eval a c129 := h 128 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c105 := h 104 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c366 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f366 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c350, some c359, some c362, some c364, some c129, some c36, some c365, some c75, some c69, some c360, some c61, some c105, some c50, some c62, some c178, some c256, some c255, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p366 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked366 : lratChecker f366 p366 = .success := by decide +kernel
theorem unsat366 : Unsatisfiable (PosFin 31) f366 := by
  apply lratCheckerSound f366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p366
  · intro a ha; simp [p366] at ha; subst a; trivial
  · exact checked366
theorem derived366 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c366 := by
  apply localUnsat_implies_entails f366 [c349, c350, c359, c362, c364, c129, c36, c365, c75, c69, c360, c61, c105, c50, c62, c178, c256, c255] c366 unsat366 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c359 := derived359 a h
  have h3 : Entails.eval a c362 := derived362 a h
  have h4 : Entails.eval a c364 := derived364 a h
  have h5 : Entails.eval a c129 := h 128 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c365 := derived365 a h
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c360 := derived360 a h
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c178 := h 177 (by decide)
  have h16 : Entails.eval a c256 := h 255 (by decide)
  have h17 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c367 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨29, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f367 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c350, some c36, some c65, some c35, some c13, some c50, some c86, some c270, some c48, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p367 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked367 : lratChecker f367 p367 = .success := by decide +kernel
theorem unsat367 : Unsatisfiable (PosFin 31) f367 := by
  apply lratCheckerSound f367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p367
  · intro a ha; simp [p367] at ha; subst a; trivial
  · exact checked367
theorem derived367 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c367 := by
  apply localUnsat_implies_entails f367 [c349, c350, c36, c65, c35, c13, c50, c86, c270, c48] c367 unsat367 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c270 := derived270 a h
  have h9 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c368 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f368 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c178, some c230, some c39, some c42, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p368 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked368 : lratChecker f368 p368 = .success := by decide +kernel
theorem unsat368 : Unsatisfiable (PosFin 31) f368 := by
  apply lratCheckerSound f368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p368
  · intro a ha; simp [p368] at ha; subst a; trivial
  · exact checked368
theorem derived368 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c368 := by
  apply localUnsat_implies_entails f368 [c349, c178, c230, c39, c42] c368 unsat368 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c369 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f369 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c364, some c129, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p369 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked369 : lratChecker f369 p369 = .success := by decide +kernel
theorem unsat369 : Unsatisfiable (PosFin 31) f369 := by
  apply lratCheckerSound f369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p369
  · intro a ha; simp [p369] at ha; subst a; trivial
  · exact checked369
theorem derived369 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c369 := by
  apply localUnsat_implies_entails f369 [c349, c364, c129] c369 unsat369 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c364 := derived364 a h
  have h2 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c370 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f370 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c366, some c368, some c367, some c369, some c163, some c131, some c152, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p370 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked370 : lratChecker f370 p370 = .success := by decide +kernel
theorem unsat370 : Unsatisfiable (PosFin 31) f370 := by
  apply lratCheckerSound f370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p370
  · intro a ha; simp [p370] at ha; subst a; trivial
  · exact checked370
theorem derived370 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c370 := by
  apply localUnsat_implies_entails f370 [c349, c366, c368, c367, c369, c163, c131, c152] c370 unsat370 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c366 := derived366 a h
  have h2 : Entails.eval a c368 := derived368 a h
  have h3 : Entails.eval a c367 := derived367 a h
  have h4 : Entails.eval a c369 := derived369 a h
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c131 := h 130 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c371 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f371 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c350, some c366, some c368, some c370, some c160, some c36, some c35, some c65, some c67, some c75, some c15, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p371 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked371 : lratChecker f371 p371 = .success := by decide +kernel
theorem unsat371 : Unsatisfiable (PosFin 31) f371 := by
  apply lratCheckerSound f371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p371
  · intro a ha; simp [p371] at ha; subst a; trivial
  · exact checked371
theorem derived371 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c371 := by
  apply localUnsat_implies_entails f371 [c350, c366, c368, c370, c160, c36, c35, c65, c67, c75, c15] c371 unsat371 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c366 := derived366 a h
  have h2 : Entails.eval a c368 := derived368 a h
  have h3 : Entails.eval a c370 := derived370 a h
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c372 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f372 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c350, some c366, some c160, some c36, some c47, some c371, some c107, some c15, some c111, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p372 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked372 : lratChecker f372 p372 = .success := by decide +kernel
theorem unsat372 : Unsatisfiable (PosFin 31) f372 := by
  apply lratCheckerSound f372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p372
  · intro a ha; simp [p372] at ha; subst a; trivial
  · exact checked372
theorem derived372 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c372 := by
  apply localUnsat_implies_entails f372 [c350, c366, c160, c36, c47, c371, c107, c15, c111] c372 unsat372 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c366 := derived366 a h
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c371 := derived371 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c373 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f373 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c350, some c371, some c366, some c160, some c36, some c47, some c372, some c13, some c113, some c91, some c105, some c111, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p373 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked373 : lratChecker f373 p373 = .success := by decide +kernel
theorem unsat373 : Unsatisfiable (PosFin 31) f373 := by
  apply lratCheckerSound f373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p373
  · intro a ha; simp [p373] at ha; subst a; trivial
  · exact checked373
theorem derived373 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c373 := by
  apply localUnsat_implies_entails f373 [c349, c350, c371, c366, c160, c36, c47, c372, c13, c113, c91, c105, c111] c373 unsat373 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c371 := derived371 a h
  have h3 : Entails.eval a c366 := derived366 a h
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c372 := derived372 a h
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c374 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f374 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c350, some c373, some c371, some c36, some c360, some c2, some c54, some c91, some c105, some c111, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p374 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked374 : lratChecker f374 p374 = .success := by decide +kernel
theorem unsat374 : Unsatisfiable (PosFin 31) f374 := by
  apply lratCheckerSound f374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p374
  · intro a ha; simp [p374] at ha; subst a; trivial
  · exact checked374
theorem derived374 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c374 := by
  apply localUnsat_implies_entails f374 [c349, c350, c373, c371, c36, c360, c2, c54, c91, c105, c111] c374 unsat374 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c373 := derived373 a h
  have h3 : Entails.eval a c371 := derived371 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c360 := derived360 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c375 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f375 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c350, some c366, some c371, some c373, some c363, some c374, some c369, some c250, some c180, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p375 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked375 : lratChecker f375 p375 = .success := by decide +kernel
theorem unsat375 : Unsatisfiable (PosFin 31) f375 := by
  apply lratCheckerSound f375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p375
  · intro a ha; simp [p375] at ha; subst a; trivial
  · exact checked375
theorem derived375 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c375 := by
  apply localUnsat_implies_entails f375 [c350, c366, c371, c373, c363, c374, c369, c250, c180] c375 unsat375 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c366 := derived366 a h
  have h2 : Entails.eval a c371 := derived371 a h
  have h3 : Entails.eval a c373 := derived373 a h
  have h4 : Entails.eval a c363 := derived363 a h
  have h5 : Entails.eval a c374 := derived374 a h
  have h6 : Entails.eval a c369 := derived369 a h
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c376 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f376 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c350, some c262, some c131, some c152, some c230, some c180, some c179, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p376 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked376 : lratChecker f376 p376 = .success := by decide +kernel
theorem unsat376 : Unsatisfiable (PosFin 31) f376 := by
  apply lratCheckerSound f376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p376
  · intro a ha; simp [p376] at ha; subst a; trivial
  · exact checked376
theorem derived376 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c376 := by
  apply localUnsat_implies_entails f376 [c349, c350, c262, c131, c152, c230, c180, c179] c376 unsat376 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c262 := derived262 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c230 := h 229 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c377 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f377 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c369, some c376, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p377 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked377 : lratChecker f377 p377 = .success := by decide +kernel
theorem unsat377 : Unsatisfiable (PosFin 31) f377 := by
  apply lratCheckerSound f377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p377
  · intro a ha; simp [p377] at ha; subst a; trivial
  · exact checked377
theorem derived377 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c377 := by
  apply localUnsat_implies_entails f377 [c369, c376] c377 unsat377 (by rfl) a
  have h0 : Entails.eval a c369 := derived369 a h
  have h1 : Entails.eval a c376 := derived376 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c378 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f378 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c375, some c350, some c377, some c133, some c63, some c363, some c180, some c13, some c46, some c16, some c18, some c92, some c261, some c77, some c22, some c159, some c61, some c70, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p378 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked378 : lratChecker f378 p378 = .success := by decide +kernel
theorem unsat378 : Unsatisfiable (PosFin 31) f378 := by
  apply lratCheckerSound f378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p378
  · intro a ha; simp [p378] at ha; subst a; trivial
  · exact checked378
theorem derived378 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c378 := by
  apply localUnsat_implies_entails f378 [c349, c375, c350, c377, c133, c63, c363, c180, c13, c46, c16, c18, c92, c261, c77, c22, c159, c61, c70] c378 unsat378 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c375 := derived375 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c377 := derived377 a h
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c363 := derived363 a h
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c261 := h 260 (by decide)
  have h14 : Entails.eval a c77 := h 76 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c159 := h 158 (by decide)
  have h17 : Entails.eval a c61 := h 60 (by decide)
  have h18 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c379 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨26, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f379 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c349, some c46, some c16, some c110, some c112, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p379 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked379 : lratChecker f379 p379 = .success := by decide +kernel
theorem unsat379 : Unsatisfiable (PosFin 31) f379 := by
  apply lratCheckerSound f379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p379
  · intro a ha; simp [p379] at ha; subst a; trivial
  · exact checked379
theorem derived379 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c379 := by
  apply localUnsat_implies_entails f379 [c375, c349, c46, c16, c110, c112] c379 unsat379 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c349 := derived349 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c380 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f380 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c350, some c349, some c375, some c377, some c133, some c378, some c230, some c152, some c46, some c379, some c68, some c13, some c95, some c49, some c137, some c50, some c226, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p380 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked380 : lratChecker f380 p380 = .success := by decide +kernel
theorem unsat380 : Unsatisfiable (PosFin 31) f380 := by
  apply lratCheckerSound f380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p380
  · intro a ha; simp [p380] at ha; subst a; trivial
  · exact checked380
theorem derived380 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c380 := by
  apply localUnsat_implies_entails f380 [c350, c349, c375, c377, c133, c378, c230, c152, c46, c379, c68, c13, c95, c49, c137, c50, c226] c380 unsat380 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c349 := derived349 a h
  have h2 : Entails.eval a c375 := derived375 a h
  have h3 : Entails.eval a c377 := derived377 a h
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c378 := derived378 a h
  have h6 : Entails.eval a c230 := h 229 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c379 := derived379 a h
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c95 := h 94 (by decide)
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c137 := h 136 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c381 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f381 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c192, some c216, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p381 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked381 : lratChecker f381 p381 = .success := by decide +kernel
theorem unsat381 : Unsatisfiable (PosFin 31) f381 := by
  apply lratCheckerSound f381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p381
  · intro a ha; simp [p381] at ha; subst a; trivial
  · exact checked381
theorem derived381 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c381 := by
  apply localUnsat_implies_entails f381 [c375, c192, c216] c381 unsat381 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c382 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f382 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c350, some c349, some c375, some c380, some c377, some c133, some c378, some c230, some c152, some c32, some c106, some c11, some c112, some c137, some c48, some c381, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p382 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked382 : lratChecker f382 p382 = .success := by decide +kernel
theorem unsat382 : Unsatisfiable (PosFin 31) f382 := by
  apply lratCheckerSound f382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p382
  · intro a ha; simp [p382] at ha; subst a; trivial
  · exact checked382
theorem derived382 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c382 := by
  apply localUnsat_implies_entails f382 [c350, c349, c375, c380, c377, c133, c378, c230, c152, c32, c106, c11, c112, c137, c48, c381] c382 unsat382 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c349 := derived349 a h
  have h2 : Entails.eval a c375 := derived375 a h
  have h3 : Entails.eval a c380 := derived380 a h
  have h4 : Entails.eval a c377 := derived377 a h
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c378 := derived378 a h
  have h7 : Entails.eval a c230 := h 229 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c48 := h 47 (by decide)
  have h15 : Entails.eval a c381 := derived381 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c383 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f383 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c350, some c349, some c377, some c380, some c382, some c1, some c13, some c88, some c91, some c113, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p383 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked383 : lratChecker f383 p383 = .success := by decide +kernel
theorem unsat383 : Unsatisfiable (PosFin 31) f383 := by
  apply lratCheckerSound f383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p383
  · intro a ha; simp [p383] at ha; subst a; trivial
  · exact checked383
theorem derived383 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c383 := by
  apply localUnsat_implies_entails f383 [c375, c350, c349, c377, c380, c382, c1, c13, c88, c91, c113] c383 unsat383 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c349 := derived349 a h
  have h3 : Entails.eval a c377 := derived377 a h
  have h4 : Entails.eval a c380 := derived380 a h
  have h5 : Entails.eval a c382 := derived382 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c384 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f384 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c350, some c349, some c377, some c1, some c13, some c88, some c91, some c113, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p384 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked384 : lratChecker f384 p384 = .success := by decide +kernel
theorem unsat384 : Unsatisfiable (PosFin 31) f384 := by
  apply lratCheckerSound f384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p384
  · intro a ha; simp [p384] at ha; subst a; trivial
  · exact checked384
theorem derived384 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c384 := by
  apply localUnsat_implies_entails f384 [c375, c350, c349, c377, c1, c13, c88, c91, c113] c384 unsat384 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c349 := derived349 a h
  have h3 : Entails.eval a c377 := derived377 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c385 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f385 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c350, some c106, some c114, some c78, some c60, some c67, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p385 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked385 : lratChecker f385 p385 = .success := by decide +kernel
theorem unsat385 : Unsatisfiable (PosFin 31) f385 := by
  apply lratCheckerSound f385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p385
  · intro a ha; simp [p385] at ha; subst a; trivial
  · exact checked385
theorem derived385 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c385 := by
  apply localUnsat_implies_entails f385 [c350, c106, c114, c78, c60, c67] c385 unsat385 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c386 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f386 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c349, some c350, some c383, some c377, some c384, some c32, some c106, some c385, some c63, some c178, some c112, some c88, some c48, some c95, some c74, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p386 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked386 : lratChecker f386 p386 = .success := by decide +kernel
theorem unsat386 : Unsatisfiable (PosFin 31) f386 := by
  apply lratCheckerSound f386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p386
  · intro a ha; simp [p386] at ha; subst a; trivial
  · exact checked386
theorem derived386 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c386 := by
  apply localUnsat_implies_entails f386 [c375, c349, c350, c383, c377, c384, c32, c106, c385, c63, c178, c112, c88, c48, c95, c74] c386 unsat386 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c349 := derived349 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c383 := derived383 a h
  have h4 : Entails.eval a c377 := derived377 a h
  have h5 : Entails.eval a c384 := derived384 a h
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c385 := derived385 a h
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c48 := h 47 (by decide)
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c387 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f387 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c350, some c349, some c386, some c46, some c383, some c364, some c377, some c63, some c136, some c178, some c379, some c116, some c95, some c106, some c105, some c122, some c101, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p387 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked387 : lratChecker f387 p387 = .success := by decide +kernel
theorem unsat387 : Unsatisfiable (PosFin 31) f387 := by
  apply lratCheckerSound f387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p387
  · intro a ha; simp [p387] at ha; subst a; trivial
  · exact checked387
theorem derived387 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c387 := by
  apply localUnsat_implies_entails f387 [c375, c350, c349, c386, c46, c383, c364, c377, c63, c136, c178, c379, c116, c95, c106, c105, c122, c101] c387 unsat387 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c350 := derived350 a h
  have h2 : Entails.eval a c349 := derived349 a h
  have h3 : Entails.eval a c386 := derived386 a h
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c383 := derived383 a h
  have h6 : Entails.eval a c364 := derived364 a h
  have h7 : Entails.eval a c377 := derived377 a h
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c379 := derived379 a h
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c95 := h 94 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c105 := h 104 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c388 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f388 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c349, some c350, some c377, some c383, some c386, some c46, some c387, some c13, some c16, some c92, some c379, some c20, some c114, some c178, some c228, some c111, some c61, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p388 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked388 : lratChecker f388 p388 = .success := by decide +kernel
theorem unsat388 : Unsatisfiable (PosFin 31) f388 := by
  apply lratCheckerSound f388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p388
  · intro a ha; simp [p388] at ha; subst a; trivial
  · exact checked388
theorem derived388 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c388 := by
  apply localUnsat_implies_entails f388 [c375, c349, c350, c377, c383, c386, c46, c387, c13, c16, c92, c379, c20, c114, c178, c228, c111, c61] c388 unsat388 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c349 := derived349 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c377 := derived377 a h
  have h4 : Entails.eval a c383 := derived383 a h
  have h5 : Entails.eval a c386 := derived386 a h
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c387 := derived387 a h
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c379 := derived379 a h
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c114 := h 113 (by decide)
  have h14 : Entails.eval a c178 := h 177 (by decide)
  have h15 : Entails.eval a c228 := h 227 (by decide)
  have h16 : Entails.eval a c111 := h 110 (by decide)
  have h17 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c389 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f389 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c388, some c160, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p389 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked389 : lratChecker f389 p389 = .success := by decide +kernel
theorem unsat389 : Unsatisfiable (PosFin 31) f389 := by
  apply lratCheckerSound f389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p389
  · intro a ha; simp [p389] at ha; subst a; trivial
  · exact checked389
theorem derived389 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c389 := by
  apply localUnsat_implies_entails f389 [c388, c160] c389 unsat389 (by rfl) a
  have h0 : Entails.eval a c388 := derived388 a h
  have h1 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c390 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f390 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c375, some c349, some c350, some c389, some c46, some c13, some c92, some c379, some c114, some c113, some c105, some c25, some c111, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p390 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked390 : lratChecker f390 p390 = .success := by decide +kernel
theorem unsat390 : Unsatisfiable (PosFin 31) f390 := by
  apply lratCheckerSound f390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p390
  · intro a ha; simp [p390] at ha; subst a; trivial
  · exact checked390
theorem derived390 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c390 := by
  apply localUnsat_implies_entails f390 [c375, c349, c350, c389, c46, c13, c92, c379, c114, c113, c105, c25, c111] c390 unsat390 (by rfl) a
  have h0 : Entails.eval a c375 := derived375 a h
  have h1 : Entails.eval a c349 := derived349 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c389 := derived389 a h
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c379 := derived379 a h
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c391 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f391 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c375, some c350, some c389, some c388, some c390, some c63, some c46, some c106, some c90, some c112, some c89, some c25, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p391 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked391 : lratChecker f391 p391 = .success := by decide +kernel
theorem unsat391 : Unsatisfiable (PosFin 31) f391 := by
  apply lratCheckerSound f391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p391
  · intro a ha; simp [p391] at ha; subst a; trivial
  · exact checked391
theorem derived391 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c391 := by
  apply localUnsat_implies_entails f391 [c349, c375, c350, c389, c388, c390, c63, c46, c106, c90, c112, c89, c25] c391 unsat391 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c375 := derived375 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c389 := derived389 a h
  have h4 : Entails.eval a c388 := derived388 a h
  have h5 : Entails.eval a c390 := derived390 a h
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c392 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f392 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c350, some c349, some c92, some c116, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p392 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked392 : lratChecker f392 p392 = .success := by decide +kernel
theorem unsat392 : Unsatisfiable (PosFin 31) f392 := by
  apply lratCheckerSound f392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p392
  · intro a ha; simp [p392] at ha; subst a; trivial
  · exact checked392
theorem derived392 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c392 := by
  apply localUnsat_implies_entails f392 [c350, c349, c92, c116] c392 unsat392 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c349 := derived349 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c393 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f393 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c349, some c375, some c46, some c391, some c392, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p393 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked393 : lratChecker f393 p393 = .success := by decide +kernel
theorem unsat393 : Unsatisfiable (PosFin 31) f393 := by
  apply lratCheckerSound f393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p393
  · intro a ha; simp [p393] at ha; subst a; trivial
  · exact checked393
theorem derived393 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c393 := by
  apply localUnsat_implies_entails f393 [c349, c375, c46, c391, c392] c393 unsat393 (by rfl) a
  have h0 : Entails.eval a c349 := derived349 a h
  have h1 : Entails.eval a c375 := derived375 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c391 := derived391 a h
  have h4 : Entails.eval a c392 := derived392 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c394 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f394 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c389, some c393, some c350, some c375, some c388, some c392, some c106, some c385, some c63, some c90, some c112, some c89, some c25, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p394 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked394 : lratChecker f394 p394 = .success := by decide +kernel
theorem unsat394 : Unsatisfiable (PosFin 31) f394 := by
  apply lratCheckerSound f394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p394
  · intro a ha; simp [p394] at ha; subst a; trivial
  · exact checked394
theorem derived394 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c394 := by
  apply localUnsat_implies_entails f394 [c389, c393, c350, c375, c388, c392, c106, c385, c63, c90, c112, c89, c25] c394 unsat394 (by rfl) a
  have h0 : Entails.eval a c389 := derived389 a h
  have h1 : Entails.eval a c393 := derived393 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c375 := derived375 a h
  have h4 : Entails.eval a c388 := derived388 a h
  have h5 : Entails.eval a c392 := derived392 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c385 := derived385 a h
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c395 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f395 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c394, some c375, some c1, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p395 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked395 : lratChecker f395 p395 = .success := by decide +kernel
theorem unsat395 : Unsatisfiable (PosFin 31) f395 := by
  apply lratCheckerSound f395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p395
  · intro a ha; simp [p395] at ha; subst a; trivial
  · exact checked395
theorem derived395 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c395 := by
  apply localUnsat_implies_entails f395 [c394, c375, c1] c395 unsat395 (by rfl) a
  have h0 : Entails.eval a c394 := derived394 a h
  have h1 : Entails.eval a c375 := derived375 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c396 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f396 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c395, some c389, some c350, some c13, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p396 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked396 : lratChecker f396 p396 = .success := by decide +kernel
theorem unsat396 : Unsatisfiable (PosFin 31) f396 := by
  apply lratCheckerSound f396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p396
  · intro a ha; simp [p396] at ha; subst a; trivial
  · exact checked396
theorem derived396 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c396 := by
  apply localUnsat_implies_entails f396 [c395, c389, c350, c13] c396 unsat396 (by rfl) a
  have h0 : Entails.eval a c395 := derived395 a h
  have h1 : Entails.eval a c389 := derived389 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c397 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f397 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c396, some c394, some c349, some c91, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p397 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked397 : lratChecker f397 p397 = .success := by decide +kernel
theorem unsat397 : Unsatisfiable (PosFin 31) f397 := by
  apply lratCheckerSound f397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p397
  · intro a ha; simp [p397] at ha; subst a; trivial
  · exact checked397
theorem derived397 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c397 := by
  apply localUnsat_implies_entails f397 [c396, c394, c349, c91] c397 unsat397 (by rfl) a
  have h0 : Entails.eval a c396 := derived396 a h
  have h1 : Entails.eval a c394 := derived394 a h
  have h2 : Entails.eval a c349 := derived349 a h
  have h3 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c398 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f398 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c397, some c395, some c389, some c113, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p398 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked398 : lratChecker f398 p398 = .success := by decide +kernel
theorem unsat398 : Unsatisfiable (PosFin 31) f398 := by
  apply lratCheckerSound f398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p398
  · intro a ha; simp [p398] at ha; subst a; trivial
  · exact checked398
theorem derived398 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c398 := by
  apply localUnsat_implies_entails f398 [c397, c395, c389, c113] c398 unsat398 (by rfl) a
  have h0 : Entails.eval a c397 := derived397 a h
  have h1 : Entails.eval a c395 := derived395 a h
  have h2 : Entails.eval a c389 := derived389 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c399 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f399 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c398, some c389, some c395, some c114, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p399 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked399 : lratChecker f399 p399 = .success := by decide +kernel
theorem unsat399 : Unsatisfiable (PosFin 31) f399 := by
  apply lratCheckerSound f399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p399
  · intro a ha; simp [p399] at ha; subst a; trivial
  · exact checked399
theorem derived399 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c399 := by
  apply localUnsat_implies_entails f399 [c398, c389, c395, c114] c399 unsat399 (by rfl) a
  have h0 : Entails.eval a c398 := derived398 a h
  have h1 : Entails.eval a c389 := derived389 a h
  have h2 : Entails.eval a c395 := derived395 a h
  have h3 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c400 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f400 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c398, some c396, some c2, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p400 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked400 : lratChecker f400 p400 = .success := by decide +kernel
theorem unsat400 : Unsatisfiable (PosFin 31) f400 := by
  apply lratCheckerSound f400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p400
  · intro a ha; simp [p400] at ha; subst a; trivial
  · exact checked400
theorem derived400 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c400 := by
  apply localUnsat_implies_entails f400 [c398, c396, c2] c400 unsat400 (by rfl) a
  have h0 : Entails.eval a c398 := derived398 a h
  have h1 : Entails.eval a c396 := derived396 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c401 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f401 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c400, some c395, some c389, some c66, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p401 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked401 : lratChecker f401 p401 = .success := by decide +kernel
theorem unsat401 : Unsatisfiable (PosFin 31) f401 := by
  apply lratCheckerSound f401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p401
  · intro a ha; simp [p401] at ha; subst a; trivial
  · exact checked401
theorem derived401 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c401 := by
  apply localUnsat_implies_entails f401 [c400, c395, c389, c66] c401 unsat401 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c395 := derived395 a h
  have h2 : Entails.eval a c389 := derived389 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c402 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f402 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c400, some c395, some c350, some c78, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p402 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked402 : lratChecker f402 p402 = .success := by decide +kernel
theorem unsat402 : Unsatisfiable (PosFin 31) f402 := by
  apply lratCheckerSound f402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p402
  · intro a ha; simp [p402] at ha; subst a; trivial
  · exact checked402
theorem derived402 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c402 := by
  apply localUnsat_implies_entails f402 [c400, c395, c350, c78] c402 unsat402 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c395 := derived395 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c403 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f403 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c389, some c350, some c61, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p403 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked403 : lratChecker f403 p403 = .success := by decide +kernel
theorem unsat403 : Unsatisfiable (PosFin 31) f403 := by
  apply lratCheckerSound f403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p403
  · intro a ha; simp [p403] at ha; subst a; trivial
  · exact checked403
theorem derived403 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c403 := by
  apply localUnsat_implies_entails f403 [c401, c389, c350, c61] c403 unsat403 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c389 := derived389 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c404 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f404 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c402, some c389, some c350, some c62, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p404 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked404 : lratChecker f404 p404 = .success := by decide +kernel
theorem unsat404 : Unsatisfiable (PosFin 31) f404 := by
  apply lratCheckerSound f404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p404
  · intro a ha; simp [p404] at ha; subst a; trivial
  · exact checked404
theorem derived404 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c404 := by
  apply localUnsat_implies_entails f404 [c402, c389, c350, c62] c404 unsat404 (by rfl) a
  have h0 : Entails.eval a c402 := derived402 a h
  have h1 : Entails.eval a c389 := derived389 a h
  have h2 : Entails.eval a c350 := derived350 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c405 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f405 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c403, some c393, some c399, some c400, some c350, some c243, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p405 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked405 : lratChecker f405 p405 = .success := by decide +kernel
theorem unsat405 : Unsatisfiable (PosFin 31) f405 := by
  apply lratCheckerSound f405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p405
  · intro a ha; simp [p405] at ha; subst a; trivial
  · exact checked405
theorem derived405 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c405 := by
  apply localUnsat_implies_entails f405 [c403, c393, c399, c400, c350, c243] c405 unsat405 (by rfl) a
  have h0 : Entails.eval a c403 := derived403 a h
  have h1 : Entails.eval a c393 := derived393 a h
  have h2 : Entails.eval a c399 := derived399 a h
  have h3 : Entails.eval a c400 := derived400 a h
  have h4 : Entails.eval a c350 := derived350 a h
  have h5 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c406 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f406 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c404, some c393, some c395, some c389, some c397, some c258, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p406 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked406 : lratChecker f406 p406 = .success := by decide +kernel
theorem unsat406 : Unsatisfiable (PosFin 31) f406 := by
  apply lratCheckerSound f406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p406
  · intro a ha; simp [p406] at ha; subst a; trivial
  · exact checked406
theorem derived406 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c406 := by
  apply localUnsat_implies_entails f406 [c404, c393, c395, c389, c397, c258] c406 unsat406 (by rfl) a
  have h0 : Entails.eval a c404 := derived404 a h
  have h1 : Entails.eval a c393 := derived393 a h
  have h2 : Entails.eval a c395 := derived395 a h
  have h3 : Entails.eval a c389 := derived389 a h
  have h4 : Entails.eval a c397 := derived397 a h
  have h5 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c407 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f407 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c406, some c405, some c396, some c398, some c3]
def p407 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked407 : lratChecker f407 p407 = .success := by decide +kernel
theorem unsat407 : Unsatisfiable (PosFin 31) f407 := by
  apply lratCheckerSound f407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p407
  · intro a ha; simp [p407] at ha; subst a; trivial
  · exact checked407
theorem derived407 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c407 := by
  apply localUnsat_implies_entails f407 [c406, c405, c396, c398, c3] c407 unsat407 (by rfl) a
  have h0 : Entails.eval a c406 := derived406 a h
  have h1 : Entails.eval a c405 := derived405 a h
  have h2 : Entails.eval a c396 := derived396 a h
  have h3 : Entails.eval a c398 := derived398 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived407

end CochromaticTwenty.Certificates.Z12Direct_5_4_9
