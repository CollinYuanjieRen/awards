import MerLeanExperiment.Certificates.FixedCore0.Steps3800_3899

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c11451 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11451 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11448, some c11449, some c11450, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p11451 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11451 : lratChecker f11451 p11451 = .success := by decide +kernel
theorem unsat11451 : Unsatisfiable (PosFin 65) f11451 := by
  apply lratCheckerSound f11451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11451
  · intro a ha; simp [p11451] at ha; subst a; trivial
  · exact checked11451
theorem derived11451 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11451 := by
  apply localUnsat_implies_entails f11451 [c11448, c11449, c11450] c11451 unsat11451 (by rfl) a
  have h0 : Entails.eval a c11448 := derived11448 a h
  have h1 : Entails.eval a c11449 := derived11449 a h
  have h2 : Entails.eval a c11450 := derived11450 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11452 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨8, by decide⟩, true), (⟨29, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11452 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11402, some c4768, some c10675, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p11452 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11452 : lratChecker f11452 p11452 = .success := by decide +kernel
theorem unsat11452 : Unsatisfiable (PosFin 65) f11452 := by
  apply lratCheckerSound f11452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11452
  · intro a ha; simp [p11452] at ha; subst a; trivial
  · exact checked11452
theorem derived11452 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11452 := by
  apply localUnsat_implies_entails f11452 [c11256, c11402, c4768, c10675] c11452 unsat11452 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c4768 := h 4767 (by decide)
  have h3 : Entails.eval a c10675 := derived10675 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11453 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11453 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11441, some c11451, some c11331, some c11170, some c11402, some c11371, some c11452, some c3307, some c3062, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11453 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11453 : lratChecker f11453 p11453 = .success := by decide +kernel
theorem unsat11453 : Unsatisfiable (PosFin 65) f11453 := by
  apply lratCheckerSound f11453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11453
  · intro a ha; simp [p11453] at ha; subst a; trivial
  · exact checked11453
theorem derived11453 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11453 := by
  apply localUnsat_implies_entails f11453 [c11441, c11451, c11331, c11170, c11402, c11371, c11452, c3307, c3062] c11453 unsat11453 (by rfl) a
  have h0 : Entails.eval a c11441 := derived11441 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c11170 := derived11170 a h
  have h4 : Entails.eval a c11402 := derived11402 a h
  have h5 : Entails.eval a c11371 := derived11371 a h
  have h6 : Entails.eval a c11452 := derived11452 a h
  have h7 : Entails.eval a c3307 := h 3306 (by decide)
  have h8 : Entails.eval a c3062 := h 3061 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11454 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11454 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11441, some c11170, some c11402, some c3079, some c3077, some c3064, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11454 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11454 : lratChecker f11454 p11454 = .success := by decide +kernel
theorem unsat11454 : Unsatisfiable (PosFin 65) f11454 := by
  apply lratCheckerSound f11454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11454
  · intro a ha; simp [p11454] at ha; subst a; trivial
  · exact checked11454
theorem derived11454 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11454 := by
  apply localUnsat_implies_entails f11454 [c11441, c11170, c11402, c3079, c3077, c3064] c11454 unsat11454 (by rfl) a
  have h0 : Entails.eval a c11441 := derived11441 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c3079 := h 3078 (by decide)
  have h4 : Entails.eval a c3077 := h 3076 (by decide)
  have h5 : Entails.eval a c3064 := h 3063 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11455 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11455 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11451, some c11441, some c11454, some c3323, some c3306, some c3321, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11455 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11455 : lratChecker f11455 p11455 = .success := by decide +kernel
theorem unsat11455 : Unsatisfiable (PosFin 65) f11455 := by
  apply lratCheckerSound f11455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11455
  · intro a ha; simp [p11455] at ha; subst a; trivial
  · exact checked11455
theorem derived11455 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11455 := by
  apply localUnsat_implies_entails f11455 [c11331, c11451, c11441, c11454, c3323, c3306, c3321] c11455 unsat11455 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c11441 := derived11441 a h
  have h3 : Entails.eval a c11454 := derived11454 a h
  have h4 : Entails.eval a c3323 := h 3322 (by decide)
  have h5 : Entails.eval a c3306 := h 3305 (by decide)
  have h6 : Entails.eval a c3321 := h 3320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11456 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11456 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c4768, some c4988, some c10675, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p11456 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11456 : lratChecker f11456 p11456 = .success := by decide +kernel
theorem unsat11456 : Unsatisfiable (PosFin 65) f11456 := by
  apply lratCheckerSound f11456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11456
  · intro a ha; simp [p11456] at ha; subst a; trivial
  · exact checked11456
theorem derived11456 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11456 := by
  apply localUnsat_implies_entails f11456 [c11402, c11256, c4768, c4988, c10675] c11456 unsat11456 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c4768 := h 4767 (by decide)
  have h3 : Entails.eval a c4988 := h 4987 (by decide)
  have h4 : Entails.eval a c10675 := derived10675 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11457 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11457 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11453, some c11455, some c11456, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11457 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11457 : lratChecker f11457 p11457 = .success := by decide +kernel
theorem unsat11457 : Unsatisfiable (PosFin 65) f11457 := by
  apply lratCheckerSound f11457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11457
  · intro a ha; simp [p11457] at ha; subst a; trivial
  · exact checked11457
theorem derived11457 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11457 := by
  apply localUnsat_implies_entails f11457 [c11453, c11455, c11456] c11457 unsat11457 (by rfl) a
  have h0 : Entails.eval a c11453 := derived11453 a h
  have h1 : Entails.eval a c11455 := derived11455 a h
  have h2 : Entails.eval a c11456 := derived11456 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11458 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11458 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10693, some c10703, some c10678, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p11458 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11458 : lratChecker f11458 p11458 = .success := by decide +kernel
theorem unsat11458 : Unsatisfiable (PosFin 65) f11458 := by
  apply lratCheckerSound f11458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11458
  · intro a ha; simp [p11458] at ha; subst a; trivial
  · exact checked11458
theorem derived11458 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11458 := by
  apply localUnsat_implies_entails f11458 [c11331, c10693, c10703, c10678] c11458 unsat11458 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10693 := derived10693 a h
  have h2 : Entails.eval a c10703 := derived10703 a h
  have h3 : Entails.eval a c10678 := derived10678 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11459 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11459 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11256, some c4767, some c4759, some c4760, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p11459 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11459 : lratChecker f11459 p11459 = .success := by decide +kernel
theorem unsat11459 : Unsatisfiable (PosFin 65) f11459 := by
  apply lratCheckerSound f11459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11459
  · intro a ha; simp [p11459] at ha; subst a; trivial
  · exact checked11459
theorem derived11459 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11459 := by
  apply localUnsat_implies_entails f11459 [c11402, c11256, c4767, c4759, c4760] c11459 unsat11459 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c4767 := h 4766 (by decide)
  have h3 : Entails.eval a c4759 := h 4758 (by decide)
  have h4 : Entails.eval a c4760 := h 4759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11460 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11460 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11402, some c11170, some c11457, some c11459, some c10703, some c11458, some c4068, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11460 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11460 : lratChecker f11460 p11460 = .success := by decide +kernel
theorem unsat11460 : Unsatisfiable (PosFin 65) f11460 := by
  apply lratCheckerSound f11460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11460
  · intro a ha; simp [p11460] at ha; subst a; trivial
  · exact checked11460
theorem derived11460 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11460 := by
  apply localUnsat_implies_entails f11460 [c11331, c11402, c11170, c11457, c11459, c10703, c11458, c4068] c11460 unsat11460 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11170 := derived11170 a h
  have h3 : Entails.eval a c11457 := derived11457 a h
  have h4 : Entails.eval a c11459 := derived11459 a h
  have h5 : Entails.eval a c10703 := derived10703 a h
  have h6 : Entails.eval a c11458 := derived11458 a h
  have h7 : Entails.eval a c4068 := h 4067 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11461 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11461 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11451, some c11441, some c11402, some c11170, some c11457, some c11460, some c11455, some c3063, some c3307, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11461 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11461 : lratChecker f11461 p11461 = .success := by decide +kernel
theorem unsat11461 : Unsatisfiable (PosFin 65) f11461 := by
  apply lratCheckerSound f11461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11461
  · intro a ha; simp [p11461] at ha; subst a; trivial
  · exact checked11461
theorem derived11461 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11461 := by
  apply localUnsat_implies_entails f11461 [c11331, c11451, c11441, c11402, c11170, c11457, c11460, c11455, c3063, c3307] c11461 unsat11461 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c11441 := derived11441 a h
  have h3 : Entails.eval a c11402 := derived11402 a h
  have h4 : Entails.eval a c11170 := derived11170 a h
  have h5 : Entails.eval a c11457 := derived11457 a h
  have h6 : Entails.eval a c11460 := derived11460 a h
  have h7 : Entails.eval a c11455 := derived11455 a h
  have h8 : Entails.eval a c3063 := h 3062 (by decide)
  have h9 : Entails.eval a c3307 := h 3306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11462 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11462 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11441, some c11402, some c11461, some c11371, some c11280, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11462 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11462 : lratChecker f11462 p11462 = .success := by decide +kernel
theorem unsat11462 : Unsatisfiable (PosFin 65) f11462 := by
  apply lratCheckerSound f11462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11462
  · intro a ha; simp [p11462] at ha; subst a; trivial
  · exact checked11462
theorem derived11462 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11462 := by
  apply localUnsat_implies_entails f11462 [c11441, c11402, c11461, c11371, c11280] c11462 unsat11462 (by rfl) a
  have h0 : Entails.eval a c11441 := derived11441 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11461 := derived11461 a h
  have h3 : Entails.eval a c11371 := derived11371 a h
  have h4 : Entails.eval a c11280 := derived11280 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11463 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11463 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11441, some c11451, some c11331, some c11462, some c11461, some c3317, some c3309, some c3315, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11463 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11463 : lratChecker f11463 p11463 = .success := by decide +kernel
theorem unsat11463 : Unsatisfiable (PosFin 65) f11463 := by
  apply lratCheckerSound f11463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11463
  · intro a ha; simp [p11463] at ha; subst a; trivial
  · exact checked11463
theorem derived11463 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11463 := by
  apply localUnsat_implies_entails f11463 [c11441, c11451, c11331, c11462, c11461, c3317, c3309, c3315] c11463 unsat11463 (by rfl) a
  have h0 : Entails.eval a c11441 := derived11441 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c11462 := derived11462 a h
  have h4 : Entails.eval a c11461 := derived11461 a h
  have h5 : Entails.eval a c3317 := h 3316 (by decide)
  have h6 : Entails.eval a c3309 := h 3308 (by decide)
  have h7 : Entails.eval a c3315 := h 3314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11464 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11464 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11441, some c11402, some c11461, some c11462, some c11463, some c11209, some c10807, some c3142, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p11464 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11464 : lratChecker f11464 p11464 = .success := by decide +kernel
theorem unsat11464 : Unsatisfiable (PosFin 65) f11464 := by
  apply lratCheckerSound f11464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11464
  · intro a ha; simp [p11464] at ha; subst a; trivial
  · exact checked11464
theorem derived11464 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11464 := by
  apply localUnsat_implies_entails f11464 [c11331, c11441, c11402, c11461, c11462, c11463, c11209, c10807, c3142] c11464 unsat11464 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11441 := derived11441 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c11461 := derived11461 a h
  have h4 : Entails.eval a c11462 := derived11462 a h
  have h5 : Entails.eval a c11463 := derived11463 a h
  have h6 : Entails.eval a c11209 := derived11209 a h
  have h7 : Entails.eval a c10807 := derived10807 a h
  have h8 : Entails.eval a c3142 := h 3141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11465 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11465 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11441, some c11402, some c10807, some c3142, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p11465 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11465 : lratChecker f11465 p11465 = .success := by decide +kernel
theorem unsat11465 : Unsatisfiable (PosFin 65) f11465 := by
  apply lratCheckerSound f11465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11465
  · intro a ha; simp [p11465] at ha; subst a; trivial
  · exact checked11465
theorem derived11465 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11465 := by
  apply localUnsat_implies_entails f11465 [c11331, c11441, c11402, c10807, c3142] c11465 unsat11465 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11441 := derived11441 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c10807 := derived10807 a h
  have h4 : Entails.eval a c3142 := h 3141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11466 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11466 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11451, some c3140, some c4602, some c3415, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p11466 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11466 : lratChecker f11466 p11466 = .success := by decide +kernel
theorem unsat11466 : Unsatisfiable (PosFin 65) f11466 := by
  apply lratCheckerSound f11466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11466
  · intro a ha; simp [p11466] at ha; subst a; trivial
  · exact checked11466
theorem derived11466 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11466 := by
  apply localUnsat_implies_entails f11466 [c11402, c11451, c3140, c4602, c3415] c11466 unsat11466 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c3140 := h 3139 (by decide)
  have h3 : Entails.eval a c4602 := h 4601 (by decide)
  have h4 : Entails.eval a c3415 := h 3414 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11467 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11467 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11402, some c11170, some c11441, some c11209, some c11465, some c11456, some c3079, some c11466, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11467 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11467 : lratChecker f11467 p11467 = .success := by decide +kernel
theorem unsat11467 : Unsatisfiable (PosFin 65) f11467 := by
  apply lratCheckerSound f11467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11467
  · intro a ha; simp [p11467] at ha; subst a; trivial
  · exact checked11467
theorem derived11467 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11467 := by
  apply localUnsat_implies_entails f11467 [c11402, c11170, c11441, c11209, c11465, c11456, c3079, c11466] c11467 unsat11467 (by rfl) a
  have h0 : Entails.eval a c11402 := derived11402 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11441 := derived11441 a h
  have h3 : Entails.eval a c11209 := derived11209 a h
  have h4 : Entails.eval a c11465 := derived11465 a h
  have h5 : Entails.eval a c11456 := derived11456 a h
  have h6 : Entails.eval a c3079 := h 3078 (by decide)
  have h7 : Entails.eval a c11466 := derived11466 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11468 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11468 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11441, some c11402, some c11256, some c11451, some c11331, some c11467, some c11456, some c3323, some c4766, some c3306, some c11425, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11468 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11468 : lratChecker f11468 p11468 = .success := by decide +kernel
theorem unsat11468 : Unsatisfiable (PosFin 65) f11468 := by
  apply lratCheckerSound f11468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11468
  · intro a ha; simp [p11468] at ha; subst a; trivial
  · exact checked11468
theorem derived11468 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11468 := by
  apply localUnsat_implies_entails f11468 [c11441, c11402, c11256, c11451, c11331, c11467, c11456, c3323, c4766, c3306, c11425] c11468 unsat11468 (by rfl) a
  have h0 : Entails.eval a c11441 := derived11441 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11256 := derived11256 a h
  have h3 : Entails.eval a c11451 := derived11451 a h
  have h4 : Entails.eval a c11331 := derived11331 a h
  have h5 : Entails.eval a c11467 := derived11467 a h
  have h6 : Entails.eval a c11456 := derived11456 a h
  have h7 : Entails.eval a c3323 := h 3322 (by decide)
  have h8 : Entails.eval a c4766 := h 4765 (by decide)
  have h9 : Entails.eval a c3306 := h 3305 (by decide)
  have h10 : Entails.eval a c11425 := derived11425 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11469 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11469 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11451, some c11441, some c11467, some c11468, some c3318, some c3317, some c3310, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11469 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11469 : lratChecker f11469 p11469 = .success := by decide +kernel
theorem unsat11469 : Unsatisfiable (PosFin 65) f11469 := by
  apply lratCheckerSound f11469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11469
  · intro a ha; simp [p11469] at ha; subst a; trivial
  · exact checked11469
theorem derived11469 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11469 := by
  apply localUnsat_implies_entails f11469 [c11331, c11451, c11441, c11467, c11468, c3318, c3317, c3310] c11469 unsat11469 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c11441 := derived11441 a h
  have h3 : Entails.eval a c11467 := derived11467 a h
  have h4 : Entails.eval a c11468 := derived11468 a h
  have h5 : Entails.eval a c3318 := h 3317 (by decide)
  have h6 : Entails.eval a c3317 := h 3316 (by decide)
  have h7 : Entails.eval a c3310 := h 3309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11470 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11470 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11441, some c11451, some c11331, some c3318, some c3317, some c3310, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11470 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11470 : lratChecker f11470 p11470 = .success := by decide +kernel
theorem unsat11470 : Unsatisfiable (PosFin 65) f11470 := by
  apply lratCheckerSound f11470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11470
  · intro a ha; simp [p11470] at ha; subst a; trivial
  · exact checked11470
theorem derived11470 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11470 := by
  apply localUnsat_implies_entails f11470 [c11441, c11451, c11331, c3318, c3317, c3310] c11470 unsat11470 (by rfl) a
  have h0 : Entails.eval a c11441 := derived11441 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c3318 := h 3317 (by decide)
  have h4 : Entails.eval a c3317 := h 3316 (by decide)
  have h5 : Entails.eval a c3310 := h 3309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11471 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11471 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11451, some c11464, some c3310, some c3322, some c3312, some c3314, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11471 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11471 : lratChecker f11471 p11471 = .success := by decide +kernel
theorem unsat11471 : Unsatisfiable (PosFin 65) f11471 := by
  apply lratCheckerSound f11471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11471
  · intro a ha; simp [p11471] at ha; subst a; trivial
  · exact checked11471
theorem derived11471 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11471 := by
  apply localUnsat_implies_entails f11471 [c11331, c11451, c11464, c3310, c3322, c3312, c3314] c11471 unsat11471 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c11464 := derived11464 a h
  have h3 : Entails.eval a c3310 := h 3309 (by decide)
  have h4 : Entails.eval a c3322 := h 3321 (by decide)
  have h5 : Entails.eval a c3312 := h 3311 (by decide)
  have h6 : Entails.eval a c3314 := h 3313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11472 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11472 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11464, some c11441, some c11331, some c11451, some c11402, some c11256, some c11377, some c11170, some c11018, some c11471, some c11470, some c3324, some c3316, some c3306, some c3303, some c3314, some c3320, some c11205, some c3301, some c11390, some c11380, some c11425, some c325, some c4744, some c320, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11472 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked11472 : lratChecker f11472 p11472 = .success := by decide +kernel
theorem unsat11472 : Unsatisfiable (PosFin 65) f11472 := by
  apply lratCheckerSound f11472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11472
  · intro a ha; simp [p11472] at ha; subst a; trivial
  · exact checked11472
theorem derived11472 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11472 := by
  apply localUnsat_implies_entails f11472 [c11464, c11441, c11331, c11451, c11402, c11256, c11377, c11170, c11018, c11471, c11470, c3324, c3316, c3306, c3303, c3314, c3320, c11205, c3301, c11390, c11380, c11425, c325, c4744, c320] c11472 unsat11472 (by rfl) a
  have h0 : Entails.eval a c11464 := derived11464 a h
  have h1 : Entails.eval a c11441 := derived11441 a h
  have h2 : Entails.eval a c11331 := derived11331 a h
  have h3 : Entails.eval a c11451 := derived11451 a h
  have h4 : Entails.eval a c11402 := derived11402 a h
  have h5 : Entails.eval a c11256 := derived11256 a h
  have h6 : Entails.eval a c11377 := derived11377 a h
  have h7 : Entails.eval a c11170 := derived11170 a h
  have h8 : Entails.eval a c11018 := derived11018 a h
  have h9 : Entails.eval a c11471 := derived11471 a h
  have h10 : Entails.eval a c11470 := derived11470 a h
  have h11 : Entails.eval a c3324 := h 3323 (by decide)
  have h12 : Entails.eval a c3316 := h 3315 (by decide)
  have h13 : Entails.eval a c3306 := h 3305 (by decide)
  have h14 : Entails.eval a c3303 := h 3302 (by decide)
  have h15 : Entails.eval a c3314 := h 3313 (by decide)
  have h16 : Entails.eval a c3320 := h 3319 (by decide)
  have h17 : Entails.eval a c11205 := derived11205 a h
  have h18 : Entails.eval a c3301 := h 3300 (by decide)
  have h19 : Entails.eval a c11390 := derived11390 a h
  have h20 : Entails.eval a c11380 := derived11380 a h
  have h21 : Entails.eval a c11425 := derived11425 a h
  have h22 : Entails.eval a c325 := h 324 (by decide)
  have h23 : Entails.eval a c4744 := h 4743 (by decide)
  have h24 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11473 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11473 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11451, some c11471, some c11472, some c3304, some c3309, some c3320, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11473 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11473 : lratChecker f11473 p11473 = .success := by decide +kernel
theorem unsat11473 : Unsatisfiable (PosFin 65) f11473 := by
  apply lratCheckerSound f11473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11473
  · intro a ha; simp [p11473] at ha; subst a; trivial
  · exact checked11473
theorem derived11473 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11473 := by
  apply localUnsat_implies_entails f11473 [c11331, c11451, c11471, c11472, c3304, c3309, c3320] c11473 unsat11473 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11451 := derived11451 a h
  have h2 : Entails.eval a c11471 := derived11471 a h
  have h3 : Entails.eval a c11472 := derived11472 a h
  have h4 : Entails.eval a c3304 := h 3303 (by decide)
  have h5 : Entails.eval a c3309 := h 3308 (by decide)
  have h6 : Entails.eval a c3320 := h 3319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11474 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11474 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11464, some c11402, some c11377, some c11441, some c11170, some c11469, some c11473, some c11209, some c3060, some c11465, some c3057, some c3056, some c3074, some c3071, some c11390, some c11380, some c3055, some c3054, some c325, some c5793, some c260, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11474 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked11474 : lratChecker f11474 p11474 = .success := by decide +kernel
theorem unsat11474 : Unsatisfiable (PosFin 65) f11474 := by
  apply lratCheckerSound f11474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11474
  · intro a ha; simp [p11474] at ha; subst a; trivial
  · exact checked11474
theorem derived11474 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11474 := by
  apply localUnsat_implies_entails f11474 [c11464, c11402, c11377, c11441, c11170, c11469, c11473, c11209, c3060, c11465, c3057, c3056, c3074, c3071, c11390, c11380, c3055, c3054, c325, c5793, c260] c11474 unsat11474 (by rfl) a
  have h0 : Entails.eval a c11464 := derived11464 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11377 := derived11377 a h
  have h3 : Entails.eval a c11441 := derived11441 a h
  have h4 : Entails.eval a c11170 := derived11170 a h
  have h5 : Entails.eval a c11469 := derived11469 a h
  have h6 : Entails.eval a c11473 := derived11473 a h
  have h7 : Entails.eval a c11209 := derived11209 a h
  have h8 : Entails.eval a c3060 := h 3059 (by decide)
  have h9 : Entails.eval a c11465 := derived11465 a h
  have h10 : Entails.eval a c3057 := h 3056 (by decide)
  have h11 : Entails.eval a c3056 := h 3055 (by decide)
  have h12 : Entails.eval a c3074 := h 3073 (by decide)
  have h13 : Entails.eval a c3071 := h 3070 (by decide)
  have h14 : Entails.eval a c11390 := derived11390 a h
  have h15 : Entails.eval a c11380 := derived11380 a h
  have h16 : Entails.eval a c3055 := h 3054 (by decide)
  have h17 : Entails.eval a c3054 := h 3053 (by decide)
  have h18 : Entails.eval a c325 := h 324 (by decide)
  have h19 : Entails.eval a c5793 := h 5792 (by decide)
  have h20 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11475 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11475 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11441, some c11474, some c11459, some c10427, some c10693, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p11475 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11475 : lratChecker f11475 p11475 = .success := by decide +kernel
theorem unsat11475 : Unsatisfiable (PosFin 65) f11475 := by
  apply lratCheckerSound f11475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11475
  · intro a ha; simp [p11475] at ha; subst a; trivial
  · exact checked11475
theorem derived11475 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11475 := by
  apply localUnsat_implies_entails f11475 [c11331, c11441, c11474, c11459, c10427, c10693] c11475 unsat11475 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11441 := derived11441 a h
  have h2 : Entails.eval a c11474 := derived11474 a h
  have h3 : Entails.eval a c11459 := derived11459 a h
  have h4 : Entails.eval a c10427 := derived10427 a h
  have h5 : Entails.eval a c10693 := derived10693 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11476 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11476 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11456, some c11475, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p11476 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11476 : lratChecker f11476 p11476 = .success := by decide +kernel
theorem unsat11476 : Unsatisfiable (PosFin 65) f11476 := by
  apply lratCheckerSound f11476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11476
  · intro a ha; simp [p11476] at ha; subst a; trivial
  · exact checked11476
theorem derived11476 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11476 := by
  apply localUnsat_implies_entails f11476 [c11456, c11475] c11476 unsat11476 (by rfl) a
  have h0 : Entails.eval a c11456 := derived11456 a h
  have h1 : Entails.eval a c11475 := derived11475 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11477 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11477 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11474, some c11256, some c11402, some c11441, some c11280, some c4981, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p11477 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11477 : lratChecker f11477 p11477 = .success := by decide +kernel
theorem unsat11477 : Unsatisfiable (PosFin 65) f11477 := by
  apply lratCheckerSound f11477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11477
  · intro a ha; simp [p11477] at ha; subst a; trivial
  · exact checked11477
theorem derived11477 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11477 := by
  apply localUnsat_implies_entails f11477 [c11474, c11256, c11402, c11441, c11280, c4981] c11477 unsat11477 (by rfl) a
  have h0 : Entails.eval a c11474 := derived11474 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11402 := derived11402 a h
  have h3 : Entails.eval a c11441 := derived11441 a h
  have h4 : Entails.eval a c11280 := derived11280 a h
  have h5 : Entails.eval a c4981 := h 4980 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11478 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11478 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11477, some c11476, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p11478 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11478 : lratChecker f11478 p11478 = .success := by decide +kernel
theorem unsat11478 : Unsatisfiable (PosFin 65) f11478 := by
  apply lratCheckerSound f11478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11478
  · intro a ha; simp [p11478] at ha; subst a; trivial
  · exact checked11478
theorem derived11478 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11478 := by
  apply localUnsat_implies_entails f11478 [c11477, c11476] c11478 unsat11478 (by rfl) a
  have h0 : Entails.eval a c11477 := derived11477 a h
  have h1 : Entails.eval a c11476 := derived11476 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11479 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11479 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11478, some c11402, some c11474, some c11441, some c11256, some c4982, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11479 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11479 : lratChecker f11479 p11479 = .success := by decide +kernel
theorem unsat11479 : Unsatisfiable (PosFin 65) f11479 := by
  apply lratCheckerSound f11479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11479
  · intro a ha; simp [p11479] at ha; subst a; trivial
  · exact checked11479
theorem derived11479 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11479 := by
  apply localUnsat_implies_entails f11479 [c11478, c11402, c11474, c11441, c11256, c4982] c11479 unsat11479 (by rfl) a
  have h0 : Entails.eval a c11478 := derived11478 a h
  have h1 : Entails.eval a c11402 := derived11402 a h
  have h2 : Entails.eval a c11474 := derived11474 a h
  have h3 : Entails.eval a c11441 := derived11441 a h
  have h4 : Entails.eval a c11256 := derived11256 a h
  have h5 : Entails.eval a c4982 := h 4981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11480 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11480 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11478, some c11441, some c11474, some c11479, some c10810, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p11480 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11480 : lratChecker f11480 p11480 = .success := by decide +kernel
theorem unsat11480 : Unsatisfiable (PosFin 65) f11480 := by
  apply lratCheckerSound f11480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11480
  · intro a ha; simp [p11480] at ha; subst a; trivial
  · exact checked11480
theorem derived11480 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11480 := by
  apply localUnsat_implies_entails f11480 [c11478, c11441, c11474, c11479, c10810] c11480 unsat11480 (by rfl) a
  have h0 : Entails.eval a c11478 := derived11478 a h
  have h1 : Entails.eval a c11441 := derived11441 a h
  have h2 : Entails.eval a c11474 := derived11474 a h
  have h3 : Entails.eval a c11479 := derived11479 a h
  have h4 : Entails.eval a c10810 := derived10810 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11481 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11481 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11478, some c11480, some c11441, some c11474, some c11256, some c4803, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p11481 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11481 : lratChecker f11481 p11481 = .success := by decide +kernel
theorem unsat11481 : Unsatisfiable (PosFin 65) f11481 := by
  apply lratCheckerSound f11481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11481
  · intro a ha; simp [p11481] at ha; subst a; trivial
  · exact checked11481
theorem derived11481 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11481 := by
  apply localUnsat_implies_entails f11481 [c11478, c11480, c11441, c11474, c11256, c4803] c11481 unsat11481 (by rfl) a
  have h0 : Entails.eval a c11478 := derived11478 a h
  have h1 : Entails.eval a c11480 := derived11480 a h
  have h2 : Entails.eval a c11441 := derived11441 a h
  have h3 : Entails.eval a c11474 := derived11474 a h
  have h4 : Entails.eval a c11256 := derived11256 a h
  have h5 : Entails.eval a c4803 := h 4802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11482 : DefaultClause 65 := directClause [] (by decide +kernel) (by decide +kernel)
def f11482 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11481, some c11478, some c11451, some c11331, some c11474, some c11441, some c4653]
def p11482 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11482 : lratChecker f11482 p11482 = .success := by decide +kernel
theorem unsat11482 : Unsatisfiable (PosFin 65) f11482 := by
  apply lratCheckerSound f11482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11482
  · intro a ha; simp [p11482] at ha; subst a; trivial
  · exact checked11482
theorem derived11482 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11482 := by
  apply localUnsat_implies_entails f11482 [c11481, c11478, c11451, c11331, c11474, c11441, c4653] c11482 unsat11482 (by rfl) a
  have h0 : Entails.eval a c11481 := derived11481 a h
  have h1 : Entails.eval a c11478 := derived11478 a h
  have h2 : Entails.eval a c11451 := derived11451 a h
  have h3 : Entails.eval a c11331 := derived11331 a h
  have h4 : Entails.eval a c11474 := derived11474 a h
  have h5 : Entails.eval a c11441 := derived11441 a h
  have h6 : Entails.eval a c4653 := h 4652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived11482

end CochromaticTwenty.Certificates.FixedCore0
