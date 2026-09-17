import MerLeanExperiment.Certificates.FixedCore0.Steps0800_0899

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8451 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8451 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8433, some c8443, some c8421, some c8446, some c8450, some c658, some c657, some c696, some c698, some c1404, some c4869, some c232, some c234, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8451 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8451 : lratChecker f8451 p8451 = .success := by decide +kernel
theorem unsat8451 : Unsatisfiable (PosFin 65) f8451 := by
  apply lratCheckerSound f8451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8451
  · intro a ha; simp [p8451] at ha; subst a; trivial
  · exact checked8451
theorem derived8451 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8451 := by
  apply localUnsat_implies_entails f8451 [c8433, c8443, c8421, c8446, c8450, c658, c657, c696, c698, c1404, c4869, c232, c234] c8451 unsat8451 (by rfl) a
  have h0 : Entails.eval a c8433 := derived8433 a h
  have h1 : Entails.eval a c8443 := derived8443 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8446 := derived8446 a h
  have h4 : Entails.eval a c8450 := derived8450 a h
  have h5 : Entails.eval a c658 := h 657 (by decide)
  have h6 : Entails.eval a c657 := h 656 (by decide)
  have h7 : Entails.eval a c696 := h 695 (by decide)
  have h8 : Entails.eval a c698 := h 697 (by decide)
  have h9 : Entails.eval a c1404 := h 1403 (by decide)
  have h10 : Entails.eval a c4869 := h 4868 (by decide)
  have h11 : Entails.eval a c232 := h 231 (by decide)
  have h12 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8452 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8452 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8433, some c8443, some c8451, some c31, some c18, some c6558, some c6596, some c6576, some c7085, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8452 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8452 : lratChecker f8452 p8452 = .success := by decide +kernel
theorem unsat8452 : Unsatisfiable (PosFin 65) f8452 := by
  apply lratCheckerSound f8452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8452
  · intro a ha; simp [p8452] at ha; subst a; trivial
  · exact checked8452
theorem derived8452 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8452 := by
  apply localUnsat_implies_entails f8452 [c8380, c8433, c8443, c8451, c31, c18, c6558, c6596, c6576, c7085] c8452 unsat8452 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8433 := derived8433 a h
  have h2 : Entails.eval a c8443 := derived8443 a h
  have h3 : Entails.eval a c8451 := derived8451 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c6558 := h 6557 (by decide)
  have h7 : Entails.eval a c6596 := h 6595 (by decide)
  have h8 : Entails.eval a c6576 := h 6575 (by decide)
  have h9 : Entails.eval a c7085 := h 7084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8453 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨49, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8453 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8432, some c5556, some c5517, some c5540, some c8425, some c5941, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8453 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8453 : lratChecker f8453 p8453 = .success := by decide +kernel
theorem unsat8453 : Unsatisfiable (PosFin 65) f8453 := by
  apply lratCheckerSound f8453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8453
  · intro a ha; simp [p8453] at ha; subst a; trivial
  · exact checked8453
theorem derived8453 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8453 := by
  apply localUnsat_implies_entails f8453 [c8432, c5556, c5517, c5540, c8425, c5941] c8453 unsat8453 (by rfl) a
  have h0 : Entails.eval a c8432 := derived8432 a h
  have h1 : Entails.eval a c5556 := h 5555 (by decide)
  have h2 : Entails.eval a c5517 := h 5516 (by decide)
  have h3 : Entails.eval a c5540 := h 5539 (by decide)
  have h4 : Entails.eval a c8425 := derived8425 a h
  have h5 : Entails.eval a c5941 := h 5940 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8454 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8454 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8438, some c8435, some c8436, some c690, some c5856, some c629, some c5973, some c5983, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8454 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8454 : lratChecker f8454 p8454 = .success := by decide +kernel
theorem unsat8454 : Unsatisfiable (PosFin 65) f8454 := by
  apply lratCheckerSound f8454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8454
  · intro a ha; simp [p8454] at ha; subst a; trivial
  · exact checked8454
theorem derived8454 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8454 := by
  apply localUnsat_implies_entails f8454 [c8438, c8435, c8436, c690, c5856, c629, c5973, c5983] c8454 unsat8454 (by rfl) a
  have h0 : Entails.eval a c8438 := derived8438 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8436 := derived8436 a h
  have h3 : Entails.eval a c690 := h 689 (by decide)
  have h4 : Entails.eval a c5856 := h 5855 (by decide)
  have h5 : Entails.eval a c629 := h 628 (by decide)
  have h6 : Entails.eval a c5973 := h 5972 (by decide)
  have h7 : Entails.eval a c5983 := h 5982 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8455 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨59, by decide⟩, false), (⟨1, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8455 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8453, some c32, some c8454, some c19, some c6562, some c709, some c6579, some c7086, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8455 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8455 : lratChecker f8455 p8455 = .success := by decide +kernel
theorem unsat8455 : Unsatisfiable (PosFin 65) f8455 := by
  apply lratCheckerSound f8455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8455
  · intro a ha; simp [p8455] at ha; subst a; trivial
  · exact checked8455
theorem derived8455 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8455 := by
  apply localUnsat_implies_entails f8455 [c8453, c32, c8454, c19, c6562, c709, c6579, c7086] c8455 unsat8455 (by rfl) a
  have h0 : Entails.eval a c8453 := derived8453 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c8454 := derived8454 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c6562 := h 6561 (by decide)
  have h5 : Entails.eval a c709 := h 708 (by decide)
  have h6 : Entails.eval a c6579 := h 6578 (by decide)
  have h7 : Entails.eval a c7086 := h 7085 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8456 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨63, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8456 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8432, some c8424, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8456 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8456 : lratChecker f8456 p8456 = .success := by decide +kernel
theorem unsat8456 : Unsatisfiable (PosFin 65) f8456 := by
  apply lratCheckerSound f8456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8456
  · intro a ha; simp [p8456] at ha; subst a; trivial
  · exact checked8456
theorem derived8456 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8456 := by
  apply localUnsat_implies_entails f8456 [c8380, c8432, c8424] c8456 unsat8456 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8432 := derived8432 a h
  have h2 : Entails.eval a c8424 := derived8424 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8457 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨26, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8457 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6102, some c5943, some c6237, some c5854, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8457 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8457 : lratChecker f8457 p8457 = .success := by decide +kernel
theorem unsat8457 : Unsatisfiable (PosFin 65) f8457 := by
  apply lratCheckerSound f8457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8457
  · intro a ha; simp [p8457] at ha; subst a; trivial
  · exact checked8457
theorem derived8457 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8457 := by
  apply localUnsat_implies_entails f8457 [c6102, c5943, c6237, c5854] c8457 unsat8457 (by rfl) a
  have h0 : Entails.eval a c6102 := h 6101 (by decide)
  have h1 : Entails.eval a c5943 := h 5942 (by decide)
  have h2 : Entails.eval a c6237 := h 6236 (by decide)
  have h3 : Entails.eval a c5854 := h 5853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8458 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8458 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8441, some c8457, some c5636, some c5682, some c5763, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8458 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8458 : lratChecker f8458 p8458 = .success := by decide +kernel
theorem unsat8458 : Unsatisfiable (PosFin 65) f8458 := by
  apply lratCheckerSound f8458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8458
  · intro a ha; simp [p8458] at ha; subst a; trivial
  · exact checked8458
theorem derived8458 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8458 := by
  apply localUnsat_implies_entails f8458 [c8441, c8457, c5636, c5682, c5763] c8458 unsat8458 (by rfl) a
  have h0 : Entails.eval a c8441 := derived8441 a h
  have h1 : Entails.eval a c8457 := derived8457 a h
  have h2 : Entails.eval a c5636 := h 5635 (by decide)
  have h3 : Entails.eval a c5682 := h 5681 (by decide)
  have h4 : Entails.eval a c5763 := h 5762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8459 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8459 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8452, some c8007, some c8455, some c8456, some c31, some c8458, some c18, some c6558, some c6596, some c6576, some c7085, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8459 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8459 : lratChecker f8459 p8459 = .success := by decide +kernel
theorem unsat8459 : Unsatisfiable (PosFin 65) f8459 := by
  apply lratCheckerSound f8459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8459
  · intro a ha; simp [p8459] at ha; subst a; trivial
  · exact checked8459
theorem derived8459 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8459 := by
  apply localUnsat_implies_entails f8459 [c8380, c8452, c8007, c8455, c8456, c31, c8458, c18, c6558, c6596, c6576, c7085] c8459 unsat8459 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8452 := derived8452 a h
  have h2 : Entails.eval a c8007 := derived8007 a h
  have h3 : Entails.eval a c8455 := derived8455 a h
  have h4 : Entails.eval a c8456 := derived8456 a h
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c8458 := derived8458 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c6558 := h 6557 (by decide)
  have h9 : Entails.eval a c6596 := h 6595 (by decide)
  have h10 : Entails.eval a c6576 := h 6575 (by decide)
  have h11 : Entails.eval a c7085 := h 7084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8460 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨49, by decide⟩, false), (⟨8, by decide⟩, false), (⟨63, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8460 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8426, some c304, some c238, some c5524, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8460 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8460 : lratChecker f8460 p8460 = .success := by decide +kernel
theorem unsat8460 : Unsatisfiable (PosFin 65) f8460 := by
  apply lratCheckerSound f8460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8460
  · intro a ha; simp [p8460] at ha; subst a; trivial
  · exact checked8460
theorem derived8460 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8460 := by
  apply localUnsat_implies_entails f8460 [c8426, c304, c238, c5524] c8460 unsat8460 (by rfl) a
  have h0 : Entails.eval a c8426 := derived8426 a h
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  have h3 : Entails.eval a c5524 := h 5523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8461 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8461 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5582, some c5606, some c8439, some c8438, some c8454, some c5955, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8461 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8461 : lratChecker f8461 p8461 = .success := by decide +kernel
theorem unsat8461 : Unsatisfiable (PosFin 65) f8461 := by
  apply lratCheckerSound f8461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8461
  · intro a ha; simp [p8461] at ha; subst a; trivial
  · exact checked8461
theorem derived8461 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8461 := by
  apply localUnsat_implies_entails f8461 [c5582, c5606, c8439, c8438, c8454, c5955] c8461 unsat8461 (by rfl) a
  have h0 : Entails.eval a c5582 := h 5581 (by decide)
  have h1 : Entails.eval a c5606 := h 5605 (by decide)
  have h2 : Entails.eval a c8439 := derived8439 a h
  have h3 : Entails.eval a c8438 := derived8438 a h
  have h4 : Entails.eval a c8454 := derived8454 a h
  have h5 : Entails.eval a c5955 := h 5954 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8462 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8462 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c1446, some c4922, some c3692, some c4228, some c8460, some c162, some c261, some c5365, some c8461, some c238, some c5660, some c666, some c698, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8462 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8462 : lratChecker f8462 p8462 = .success := by decide +kernel
theorem unsat8462 : Unsatisfiable (PosFin 65) f8462 := by
  apply lratCheckerSound f8462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8462
  · intro a ha; simp [p8462] at ha; subst a; trivial
  · exact checked8462
theorem derived8462 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8462 := by
  apply localUnsat_implies_entails f8462 [c8421, c1446, c4922, c3692, c4228, c8460, c162, c261, c5365, c8461, c238, c5660, c666, c698] c8462 unsat8462 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c1446 := h 1445 (by decide)
  have h2 : Entails.eval a c4922 := h 4921 (by decide)
  have h3 : Entails.eval a c3692 := h 3691 (by decide)
  have h4 : Entails.eval a c4228 := h 4227 (by decide)
  have h5 : Entails.eval a c8460 := derived8460 a h
  have h6 : Entails.eval a c162 := h 161 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c5365 := h 5364 (by decide)
  have h9 : Entails.eval a c8461 := derived8461 a h
  have h10 : Entails.eval a c238 := h 237 (by decide)
  have h11 : Entails.eval a c5660 := h 5659 (by decide)
  have h12 : Entails.eval a c666 := h 665 (by decide)
  have h13 : Entails.eval a c698 := h 697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8463 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨63, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8463 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5524, some c5547, some c5562, some c5960, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p8463 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8463 : lratChecker f8463 p8463 = .success := by decide +kernel
theorem unsat8463 : Unsatisfiable (PosFin 65) f8463 := by
  apply lratCheckerSound f8463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8463
  · intro a ha; simp [p8463] at ha; subst a; trivial
  · exact checked8463
theorem derived8463 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8463 := by
  apply localUnsat_implies_entails f8463 [c5524, c5547, c5562, c5960] c8463 unsat8463 (by rfl) a
  have h0 : Entails.eval a c5524 := h 5523 (by decide)
  have h1 : Entails.eval a c5547 := h 5546 (by decide)
  have h2 : Entails.eval a c5562 := h 5561 (by decide)
  have h3 : Entails.eval a c5960 := h 5959 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8464 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨49, by decide⟩, true), (⟨8, by decide⟩, false), (⟨63, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8464 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c139, some c238, some c213, some c880, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8464 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8464 : lratChecker f8464 p8464 = .success := by decide +kernel
theorem unsat8464 : Unsatisfiable (PosFin 65) f8464 := by
  apply lratCheckerSound f8464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8464
  · intro a ha; simp [p8464] at ha; subst a; trivial
  · exact checked8464
theorem derived8464 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8464 := by
  apply localUnsat_implies_entails f8464 [c8380, c139, c238, c213, c880] c8464 unsat8464 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c880 := h 879 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8465 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8465 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8421, some c8459, some c1295, some c1446, some c1107, some c4922, some c3692, some c4228, some c8462, some c4450, some c4613, some c8464, some c8463, some c162, some c261, some c267, some c5339, some c5335, some c5325, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8465 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8465 : lratChecker f8465 p8465 = .success := by decide +kernel
theorem unsat8465 : Unsatisfiable (PosFin 65) f8465 := by
  apply lratCheckerSound f8465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8465
  · intro a ha; simp [p8465] at ha; subst a; trivial
  · exact checked8465
theorem derived8465 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8465 := by
  apply localUnsat_implies_entails f8465 [c8380, c8421, c8459, c1295, c1446, c1107, c4922, c3692, c4228, c8462, c4450, c4613, c8464, c8463, c162, c261, c267, c5339, c5335, c5325] c8465 unsat8465 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8459 := derived8459 a h
  have h3 : Entails.eval a c1295 := h 1294 (by decide)
  have h4 : Entails.eval a c1446 := h 1445 (by decide)
  have h5 : Entails.eval a c1107 := h 1106 (by decide)
  have h6 : Entails.eval a c4922 := h 4921 (by decide)
  have h7 : Entails.eval a c3692 := h 3691 (by decide)
  have h8 : Entails.eval a c4228 := h 4227 (by decide)
  have h9 : Entails.eval a c8462 := derived8462 a h
  have h10 : Entails.eval a c4450 := h 4449 (by decide)
  have h11 : Entails.eval a c4613 := h 4612 (by decide)
  have h12 : Entails.eval a c8464 := derived8464 a h
  have h13 : Entails.eval a c8463 := derived8463 a h
  have h14 : Entails.eval a c162 := h 161 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c267 := h 266 (by decide)
  have h17 : Entails.eval a c5339 := h 5338 (by decide)
  have h18 : Entails.eval a c5335 := h 5334 (by decide)
  have h19 : Entails.eval a c5325 := h 5324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8466 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨19, by decide⟩, true), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8466 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1271, some c1421, some c4728, some c8432, some c8456, some c653, some c654, some c4447, some c5952, some c998, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8466 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8466 : lratChecker f8466 p8466 = .success := by decide +kernel
theorem unsat8466 : Unsatisfiable (PosFin 65) f8466 := by
  apply lratCheckerSound f8466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8466
  · intro a ha; simp [p8466] at ha; subst a; trivial
  · exact checked8466
theorem derived8466 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8466 := by
  apply localUnsat_implies_entails f8466 [c1271, c1421, c4728, c8432, c8456, c653, c654, c4447, c5952, c998] c8466 unsat8466 (by rfl) a
  have h0 : Entails.eval a c1271 := h 1270 (by decide)
  have h1 : Entails.eval a c1421 := h 1420 (by decide)
  have h2 : Entails.eval a c4728 := h 4727 (by decide)
  have h3 : Entails.eval a c8432 := derived8432 a h
  have h4 : Entails.eval a c8456 := derived8456 a h
  have h5 : Entails.eval a c653 := h 652 (by decide)
  have h6 : Entails.eval a c654 := h 653 (by decide)
  have h7 : Entails.eval a c4447 := h 4446 (by decide)
  have h8 : Entails.eval a c5952 := h 5951 (by decide)
  have h9 : Entails.eval a c998 := h 997 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8467 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8467 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8465, some c1271, some c1421, some c4728, some c3154, some c8421, some c4904, some c8466, some c4478, some c8460, some c8463, some c8464, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8467 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8467 : lratChecker f8467 p8467 = .success := by decide +kernel
theorem unsat8467 : Unsatisfiable (PosFin 65) f8467 := by
  apply lratCheckerSound f8467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8467
  · intro a ha; simp [p8467] at ha; subst a; trivial
  · exact checked8467
theorem derived8467 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8467 := by
  apply localUnsat_implies_entails f8467 [c8465, c1271, c1421, c4728, c3154, c8421, c4904, c8466, c4478, c8460, c8463, c8464] c8467 unsat8467 (by rfl) a
  have h0 : Entails.eval a c8465 := derived8465 a h
  have h1 : Entails.eval a c1271 := h 1270 (by decide)
  have h2 : Entails.eval a c1421 := h 1420 (by decide)
  have h3 : Entails.eval a c4728 := h 4727 (by decide)
  have h4 : Entails.eval a c3154 := h 3153 (by decide)
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c4904 := h 4903 (by decide)
  have h7 : Entails.eval a c8466 := derived8466 a h
  have h8 : Entails.eval a c4478 := h 4477 (by decide)
  have h9 : Entails.eval a c8460 := derived8460 a h
  have h10 : Entails.eval a c8463 := derived8463 a h
  have h11 : Entails.eval a c8464 := derived8464 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8468 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8468 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8465, some c1271, some c1421, some c4728, some c3197, some c4189, some c8467, some c146, some c270, some c259, some c5326, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8468 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8468 : lratChecker f8468 p8468 = .success := by decide +kernel
theorem unsat8468 : Unsatisfiable (PosFin 65) f8468 := by
  apply lratCheckerSound f8468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8468
  · intro a ha; simp [p8468] at ha; subst a; trivial
  · exact checked8468
theorem derived8468 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8468 := by
  apply localUnsat_implies_entails f8468 [c8421, c8465, c1271, c1421, c4728, c3197, c4189, c8467, c146, c270, c259, c5326] c8468 unsat8468 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8465 := derived8465 a h
  have h2 : Entails.eval a c1271 := h 1270 (by decide)
  have h3 : Entails.eval a c1421 := h 1420 (by decide)
  have h4 : Entails.eval a c4728 := h 4727 (by decide)
  have h5 : Entails.eval a c3197 := h 3196 (by decide)
  have h6 : Entails.eval a c4189 := h 4188 (by decide)
  have h7 : Entails.eval a c8467 := derived8467 a h
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c259 := h 258 (by decide)
  have h11 : Entails.eval a c5326 := h 5325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8469 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨63, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8469 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5549, some c5533, some c5567, some c5963, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p8469 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8469 : lratChecker f8469 p8469 = .success := by decide +kernel
theorem unsat8469 : Unsatisfiable (PosFin 65) f8469 := by
  apply lratCheckerSound f8469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8469
  · intro a ha; simp [p8469] at ha; subst a; trivial
  · exact checked8469
theorem derived8469 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8469 := by
  apply localUnsat_implies_entails f8469 [c5549, c5533, c5567, c5963] c8469 unsat8469 (by rfl) a
  have h0 : Entails.eval a c5549 := h 5548 (by decide)
  have h1 : Entails.eval a c5533 := h 5532 (by decide)
  have h2 : Entails.eval a c5567 := h 5566 (by decide)
  have h3 : Entails.eval a c5963 := h 5962 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8470 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨19, by decide⟩, true), (⟨57, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8470 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1303, some c1238, some c4471, some c8469, some c143, some c223, some c5390, some c5402, some c8431, some c669, some c702, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8470 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8470 : lratChecker f8470 p8470 = .success := by decide +kernel
theorem unsat8470 : Unsatisfiable (PosFin 65) f8470 := by
  apply lratCheckerSound f8470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8470
  · intro a ha; simp [p8470] at ha; subst a; trivial
  · exact checked8470
theorem derived8470 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8470 := by
  apply localUnsat_implies_entails f8470 [c1303, c1238, c4471, c8469, c143, c223, c5390, c5402, c8431, c669, c702] c8470 unsat8470 (by rfl) a
  have h0 : Entails.eval a c1303 := h 1302 (by decide)
  have h1 : Entails.eval a c1238 := h 1237 (by decide)
  have h2 : Entails.eval a c4471 := h 4470 (by decide)
  have h3 : Entails.eval a c8469 := derived8469 a h
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c223 := h 222 (by decide)
  have h6 : Entails.eval a c5390 := h 5389 (by decide)
  have h7 : Entails.eval a c5402 := h 5401 (by decide)
  have h8 : Entails.eval a c8431 := derived8431 a h
  have h9 : Entails.eval a c669 := h 668 (by decide)
  have h10 : Entails.eval a c702 := h 701 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8471 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨57, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8471 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8421, some c8470, some c1295, some c1446, some c1107, some c4922, some c8460, some c8463, some c4450, some c4613, some c8464, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8471 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8471 : lratChecker f8471 p8471 = .success := by decide +kernel
theorem unsat8471 : Unsatisfiable (PosFin 65) f8471 := by
  apply lratCheckerSound f8471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8471
  · intro a ha; simp [p8471] at ha; subst a; trivial
  · exact checked8471
theorem derived8471 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8471 := by
  apply localUnsat_implies_entails f8471 [c8380, c8421, c8470, c1295, c1446, c1107, c4922, c8460, c8463, c4450, c4613, c8464] c8471 unsat8471 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8470 := derived8470 a h
  have h3 : Entails.eval a c1295 := h 1294 (by decide)
  have h4 : Entails.eval a c1446 := h 1445 (by decide)
  have h5 : Entails.eval a c1107 := h 1106 (by decide)
  have h6 : Entails.eval a c4922 := h 4921 (by decide)
  have h7 : Entails.eval a c8460 := derived8460 a h
  have h8 : Entails.eval a c8463 := derived8463 a h
  have h9 : Entails.eval a c4450 := h 4449 (by decide)
  have h10 : Entails.eval a c4613 := h 4612 (by decide)
  have h11 : Entails.eval a c8464 := derived8464 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8472 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨19, by decide⟩, false), (⟨57, by decide⟩, true), (⟨56, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8472 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1303, some c1238, some c166, some c4740, some c3620, some c278, some c4229, some c5340, some c262, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8472 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8472 : lratChecker f8472 p8472 = .success := by decide +kernel
theorem unsat8472 : Unsatisfiable (PosFin 65) f8472 := by
  apply lratCheckerSound f8472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8472
  · intro a ha; simp [p8472] at ha; subst a; trivial
  · exact checked8472
theorem derived8472 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8472 := by
  apply localUnsat_implies_entails f8472 [c1303, c1238, c166, c4740, c3620, c278, c4229, c5340, c262] c8472 unsat8472 (by rfl) a
  have h0 : Entails.eval a c1303 := h 1302 (by decide)
  have h1 : Entails.eval a c1238 := h 1237 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c4740 := h 4739 (by decide)
  have h4 : Entails.eval a c3620 := h 3619 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c4229 := h 4228 (by decide)
  have h7 : Entails.eval a c5340 := h 5339 (by decide)
  have h8 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8473 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨21, by decide⟩, true), (⟨63, by decide⟩, false), (⟨19, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8473 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c5582, some c5606, some c6003, some c5960, some c5678, some c8438, some c5761, some c5803, some c6160, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8473 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8473 : lratChecker f8473 p8473 = .success := by decide +kernel
theorem unsat8473 : Unsatisfiable (PosFin 65) f8473 := by
  apply lratCheckerSound f8473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8473
  · intro a ha; simp [p8473] at ha; subst a; trivial
  · exact checked8473
theorem derived8473 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8473 := by
  apply localUnsat_implies_entails f8473 [c8380, c5582, c5606, c6003, c5960, c5678, c8438, c5761, c5803, c6160] c8473 unsat8473 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c5582 := h 5581 (by decide)
  have h2 : Entails.eval a c5606 := h 5605 (by decide)
  have h3 : Entails.eval a c6003 := h 6002 (by decide)
  have h4 : Entails.eval a c5960 := h 5959 (by decide)
  have h5 : Entails.eval a c5678 := h 5677 (by decide)
  have h6 : Entails.eval a c8438 := derived8438 a h
  have h7 : Entails.eval a c5761 := h 5760 (by decide)
  have h8 : Entails.eval a c5803 := h 5802 (by decide)
  have h9 : Entails.eval a c6160 := h 6159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8474 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨63, by decide⟩, false), (⟨54, by decide⟩, false), (⟨35, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8474 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6599, some c6565, some c6585, some c7089, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p8474 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8474 : lratChecker f8474 p8474 = .success := by decide +kernel
theorem unsat8474 : Unsatisfiable (PosFin 65) f8474 := by
  apply lratCheckerSound f8474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8474
  · intro a ha; simp [p8474] at ha; subst a; trivial
  · exact checked8474
theorem derived8474 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8474 := by
  apply localUnsat_implies_entails f8474 [c6599, c6565, c6585, c7089] c8474 unsat8474 (by rfl) a
  have h0 : Entails.eval a c6599 := h 6598 (by decide)
  have h1 : Entails.eval a c6565 := h 6564 (by decide)
  have h2 : Entails.eval a c6585 := h 6584 (by decide)
  have h3 : Entails.eval a c7089 := h 7088 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8475 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8475 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8471, some c8472, some c1446, some c4922, some c162, some c40, some c3692, some c4228, some c261, some c5365, some c8473, some c24, some c8474, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8475 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8475 : lratChecker f8475 p8475 = .success := by decide +kernel
theorem unsat8475 : Unsatisfiable (PosFin 65) f8475 := by
  apply lratCheckerSound f8475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8475
  · intro a ha; simp [p8475] at ha; subst a; trivial
  · exact checked8475
theorem derived8475 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8475 := by
  apply localUnsat_implies_entails f8475 [c8421, c8471, c8472, c1446, c4922, c162, c40, c3692, c4228, c261, c5365, c8473, c24, c8474] c8475 unsat8475 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8471 := derived8471 a h
  have h2 : Entails.eval a c8472 := derived8472 a h
  have h3 : Entails.eval a c1446 := h 1445 (by decide)
  have h4 : Entails.eval a c4922 := h 4921 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c3692 := h 3691 (by decide)
  have h8 : Entails.eval a c4228 := h 4227 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c5365 := h 5364 (by decide)
  have h11 : Entails.eval a c8473 := derived8473 a h
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c8474 := derived8474 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8476 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8476 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8475, some c8468, some c8380, some c8466, some c8432, some c8456, some c5523, some c8425, some c653, some c654, some c628, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8476 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8476 : lratChecker f8476 p8476 = .success := by decide +kernel
theorem unsat8476 : Unsatisfiable (PosFin 65) f8476 := by
  apply lratCheckerSound f8476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8476
  · intro a ha; simp [p8476] at ha; subst a; trivial
  · exact checked8476
theorem derived8476 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8476 := by
  apply localUnsat_implies_entails f8476 [c8475, c8468, c8380, c8466, c8432, c8456, c5523, c8425, c653, c654, c628] c8476 unsat8476 (by rfl) a
  have h0 : Entails.eval a c8475 := derived8475 a h
  have h1 : Entails.eval a c8468 := derived8468 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c8466 := derived8466 a h
  have h4 : Entails.eval a c8432 := derived8432 a h
  have h5 : Entails.eval a c8456 := derived8456 a h
  have h6 : Entails.eval a c5523 := h 5522 (by decide)
  have h7 : Entails.eval a c8425 := derived8425 a h
  have h8 : Entails.eval a c653 := h 652 (by decide)
  have h9 : Entails.eval a c654 := h 653 (by decide)
  have h10 : Entails.eval a c628 := h 627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8477 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8477 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8475, some c8468, some c1444, some c1106, some c8421, some c4921, some c3659, some c4668, some c3168, some c4479, some c8476, some c161, some c276, some c5420, some c5437, some c5900, some c236, some c1013, some c889, some c5836, some c5587, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8477 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8477 : lratChecker f8477 p8477 = .success := by decide +kernel
theorem unsat8477 : Unsatisfiable (PosFin 65) f8477 := by
  apply lratCheckerSound f8477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8477
  · intro a ha; simp [p8477] at ha; subst a; trivial
  · exact checked8477
theorem derived8477 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8477 := by
  apply localUnsat_implies_entails f8477 [c8380, c8475, c8468, c1444, c1106, c8421, c4921, c3659, c4668, c3168, c4479, c8476, c161, c276, c5420, c5437, c5900, c236, c1013, c889, c5836, c5587] c8477 unsat8477 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8475 := derived8475 a h
  have h2 : Entails.eval a c8468 := derived8468 a h
  have h3 : Entails.eval a c1444 := h 1443 (by decide)
  have h4 : Entails.eval a c1106 := h 1105 (by decide)
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c4921 := h 4920 (by decide)
  have h7 : Entails.eval a c3659 := h 3658 (by decide)
  have h8 : Entails.eval a c4668 := h 4667 (by decide)
  have h9 : Entails.eval a c3168 := h 3167 (by decide)
  have h10 : Entails.eval a c4479 := h 4478 (by decide)
  have h11 : Entails.eval a c8476 := derived8476 a h
  have h12 : Entails.eval a c161 := h 160 (by decide)
  have h13 : Entails.eval a c276 := h 275 (by decide)
  have h14 : Entails.eval a c5420 := h 5419 (by decide)
  have h15 : Entails.eval a c5437 := h 5436 (by decide)
  have h16 : Entails.eval a c5900 := h 5899 (by decide)
  have h17 : Entails.eval a c236 := h 235 (by decide)
  have h18 : Entails.eval a c1013 := h 1012 (by decide)
  have h19 : Entails.eval a c889 := h 888 (by decide)
  have h20 : Entails.eval a c5836 := h 5835 (by decide)
  have h21 : Entails.eval a c5587 := h 5586 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8478 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨63, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8478 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8460, some c8463, some c8464, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8478 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8478 : lratChecker f8478 p8478 = .success := by decide +kernel
theorem unsat8478 : Unsatisfiable (PosFin 65) f8478 := by
  apply lratCheckerSound f8478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8478
  · intro a ha; simp [p8478] at ha; subst a; trivial
  · exact checked8478
theorem derived8478 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8478 := by
  apply localUnsat_implies_entails f8478 [c8460, c8463, c8464] c8478 unsat8478 (by rfl) a
  have h0 : Entails.eval a c8460 := derived8460 a h
  have h1 : Entails.eval a c8463 := derived8463 a h
  have h2 : Entails.eval a c8464 := derived8464 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8479 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8479 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8421, some c8475, some c8468, some c1444, some c1106, some c4921, some c3659, some c4668, some c3168, some c4479, some c8477, some c3692, some c4228, some c8478, some c39, some c161, some c261, some c8474, some c5365, some c23, some c8473, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8479 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8479 : lratChecker f8479 p8479 = .success := by decide +kernel
theorem unsat8479 : Unsatisfiable (PosFin 65) f8479 := by
  apply lratCheckerSound f8479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8479
  · intro a ha; simp [p8479] at ha; subst a; trivial
  · exact checked8479
theorem derived8479 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8479 := by
  apply localUnsat_implies_entails f8479 [c8380, c8421, c8475, c8468, c1444, c1106, c4921, c3659, c4668, c3168, c4479, c8477, c3692, c4228, c8478, c39, c161, c261, c8474, c5365, c23, c8473] c8479 unsat8479 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8475 := derived8475 a h
  have h3 : Entails.eval a c8468 := derived8468 a h
  have h4 : Entails.eval a c1444 := h 1443 (by decide)
  have h5 : Entails.eval a c1106 := h 1105 (by decide)
  have h6 : Entails.eval a c4921 := h 4920 (by decide)
  have h7 : Entails.eval a c3659 := h 3658 (by decide)
  have h8 : Entails.eval a c4668 := h 4667 (by decide)
  have h9 : Entails.eval a c3168 := h 3167 (by decide)
  have h10 : Entails.eval a c4479 := h 4478 (by decide)
  have h11 : Entails.eval a c8477 := derived8477 a h
  have h12 : Entails.eval a c3692 := h 3691 (by decide)
  have h13 : Entails.eval a c4228 := h 4227 (by decide)
  have h14 : Entails.eval a c8478 := derived8478 a h
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c261 := h 260 (by decide)
  have h18 : Entails.eval a c8474 := derived8474 a h
  have h19 : Entails.eval a c5365 := h 5364 (by decide)
  have h20 : Entails.eval a c23 := h 22 (by decide)
  have h21 : Entails.eval a c8473 := derived8473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8480 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨57, by decide⟩, false), (⟨19, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8480 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5546, some c5560, some c5519, some c5958, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p8480 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8480 : lratChecker f8480 p8480 = .success := by decide +kernel
theorem unsat8480 : Unsatisfiable (PosFin 65) f8480 := by
  apply lratCheckerSound f8480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8480
  · intro a ha; simp [p8480] at ha; subst a; trivial
  · exact checked8480
theorem derived8480 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8480 := by
  apply localUnsat_implies_entails f8480 [c5546, c5560, c5519, c5958] c8480 unsat8480 (by rfl) a
  have h0 : Entails.eval a c5546 := h 5545 (by decide)
  have h1 : Entails.eval a c5560 := h 5559 (by decide)
  have h2 : Entails.eval a c5519 := h 5518 (by decide)
  have h3 : Entails.eval a c5958 := h 5957 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8481 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8481 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8479, some c8421, some c1228, some c1157, some c4919, some c4736, some c8480, some c233, some c8426, some c888, some c887, some c5610, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8481 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8481 : lratChecker f8481 p8481 = .success := by decide +kernel
theorem unsat8481 : Unsatisfiable (PosFin 65) f8481 := by
  apply lratCheckerSound f8481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8481
  · intro a ha; simp [p8481] at ha; subst a; trivial
  · exact checked8481
theorem derived8481 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8481 := by
  apply localUnsat_implies_entails f8481 [c8479, c8421, c1228, c1157, c4919, c4736, c8480, c233, c8426, c888, c887, c5610] c8481 unsat8481 (by rfl) a
  have h0 : Entails.eval a c8479 := derived8479 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c1228 := h 1227 (by decide)
  have h3 : Entails.eval a c1157 := h 1156 (by decide)
  have h4 : Entails.eval a c4919 := h 4918 (by decide)
  have h5 : Entails.eval a c4736 := h 4735 (by decide)
  have h6 : Entails.eval a c8480 := derived8480 a h
  have h7 : Entails.eval a c233 := h 232 (by decide)
  have h8 : Entails.eval a c8426 := derived8426 a h
  have h9 : Entails.eval a c888 := h 887 (by decide)
  have h10 : Entails.eval a c887 := h 886 (by decide)
  have h11 : Entails.eval a c5610 := h 5609 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8482 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8482 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8479, some c8421, some c8481, some c1303, some c1238, some c8469, some c4471, some c4740, some c223, some c3620, some c5715, some c5760, some c887, some c4229, some c961, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8482 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8482 : lratChecker f8482 p8482 = .success := by decide +kernel
theorem unsat8482 : Unsatisfiable (PosFin 65) f8482 := by
  apply lratCheckerSound f8482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8482
  · intro a ha; simp [p8482] at ha; subst a; trivial
  · exact checked8482
theorem derived8482 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8482 := by
  apply localUnsat_implies_entails f8482 [c8479, c8421, c8481, c1303, c1238, c8469, c4471, c4740, c223, c3620, c5715, c5760, c887, c4229, c961] c8482 unsat8482 (by rfl) a
  have h0 : Entails.eval a c8479 := derived8479 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8481 := derived8481 a h
  have h3 : Entails.eval a c1303 := h 1302 (by decide)
  have h4 : Entails.eval a c1238 := h 1237 (by decide)
  have h5 : Entails.eval a c8469 := derived8469 a h
  have h6 : Entails.eval a c4471 := h 4470 (by decide)
  have h7 : Entails.eval a c4740 := h 4739 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c3620 := h 3619 (by decide)
  have h10 : Entails.eval a c5715 := h 5714 (by decide)
  have h11 : Entails.eval a c5760 := h 5759 (by decide)
  have h12 : Entails.eval a c887 := h 886 (by decide)
  have h13 : Entails.eval a c4229 := h 4228 (by decide)
  have h14 : Entails.eval a c961 := h 960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8483 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8483 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8479, some c8421, some c8482, some c8472, some c1228, some c1157, some c157, some c4736, some c275, some c5436, some c5419, some c6204, some c889, some c6037, some c680, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8483 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8483 : lratChecker f8483 p8483 = .success := by decide +kernel
theorem unsat8483 : Unsatisfiable (PosFin 65) f8483 := by
  apply lratCheckerSound f8483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8483
  · intro a ha; simp [p8483] at ha; subst a; trivial
  · exact checked8483
theorem derived8483 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8483 := by
  apply localUnsat_implies_entails f8483 [c8479, c8421, c8482, c8472, c1228, c1157, c157, c4736, c275, c5436, c5419, c6204, c889, c6037, c680] c8483 unsat8483 (by rfl) a
  have h0 : Entails.eval a c8479 := derived8479 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8482 := derived8482 a h
  have h3 : Entails.eval a c8472 := derived8472 a h
  have h4 : Entails.eval a c1228 := h 1227 (by decide)
  have h5 : Entails.eval a c1157 := h 1156 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c4736 := h 4735 (by decide)
  have h8 : Entails.eval a c275 := h 274 (by decide)
  have h9 : Entails.eval a c5436 := h 5435 (by decide)
  have h10 : Entails.eval a c5419 := h 5418 (by decide)
  have h11 : Entails.eval a c6204 := h 6203 (by decide)
  have h12 : Entails.eval a c889 := h 888 (by decide)
  have h13 : Entails.eval a c6037 := h 6036 (by decide)
  have h14 : Entails.eval a c680 := h 679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8484 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨63, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8484 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c1446, some c4922, some c3692, some c4228, some c8463, some c139, some c24, some c238, some c8474, some c5773, some c5778, some c471, some c6215, some c5660, some c6608, some c5466, some c5365, some c385, some c388, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8484 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8484 : lratChecker f8484 p8484 = .success := by decide +kernel
theorem unsat8484 : Unsatisfiable (PosFin 65) f8484 := by
  apply lratCheckerSound f8484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8484
  · intro a ha; simp [p8484] at ha; subst a; trivial
  · exact checked8484
theorem derived8484 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8484 := by
  apply localUnsat_implies_entails f8484 [c8421, c1446, c4922, c3692, c4228, c8463, c139, c24, c238, c8474, c5773, c5778, c471, c6215, c5660, c6608, c5466, c5365, c385, c388] c8484 unsat8484 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c1446 := h 1445 (by decide)
  have h2 : Entails.eval a c4922 := h 4921 (by decide)
  have h3 : Entails.eval a c3692 := h 3691 (by decide)
  have h4 : Entails.eval a c4228 := h 4227 (by decide)
  have h5 : Entails.eval a c8463 := derived8463 a h
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c238 := h 237 (by decide)
  have h9 : Entails.eval a c8474 := derived8474 a h
  have h10 : Entails.eval a c5773 := h 5772 (by decide)
  have h11 : Entails.eval a c5778 := h 5777 (by decide)
  have h12 : Entails.eval a c471 := h 470 (by decide)
  have h13 : Entails.eval a c6215 := h 6214 (by decide)
  have h14 : Entails.eval a c5660 := h 5659 (by decide)
  have h15 : Entails.eval a c6608 := h 6607 (by decide)
  have h16 : Entails.eval a c5466 := h 5465 (by decide)
  have h17 : Entails.eval a c5365 := h 5364 (by decide)
  have h18 : Entails.eval a c385 := h 384 (by decide)
  have h19 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8485 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8485 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8483, some c1446, some c4922, some c3692, some c4228, some c8484, some c40, some c261, some c8474, some c413, some c24, some c459, some c5582, some c6898, some c6883, some c105, some c111, some c103, some c101, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8485 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8485 : lratChecker f8485 p8485 = .success := by decide +kernel
theorem unsat8485 : Unsatisfiable (PosFin 65) f8485 := by
  apply lratCheckerSound f8485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8485
  · intro a ha; simp [p8485] at ha; subst a; trivial
  · exact checked8485
theorem derived8485 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8485 := by
  apply localUnsat_implies_entails f8485 [c8421, c8483, c1446, c4922, c3692, c4228, c8484, c40, c261, c8474, c413, c24, c459, c5582, c6898, c6883, c105, c111, c103, c101] c8485 unsat8485 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8483 := derived8483 a h
  have h2 : Entails.eval a c1446 := h 1445 (by decide)
  have h3 : Entails.eval a c4922 := h 4921 (by decide)
  have h4 : Entails.eval a c3692 := h 3691 (by decide)
  have h5 : Entails.eval a c4228 := h 4227 (by decide)
  have h6 : Entails.eval a c8484 := derived8484 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c8474 := derived8474 a h
  have h10 : Entails.eval a c413 := h 412 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c459 := h 458 (by decide)
  have h13 : Entails.eval a c5582 := h 5581 (by decide)
  have h14 : Entails.eval a c6898 := h 6897 (by decide)
  have h15 : Entails.eval a c6883 := h 6882 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c111 := h 110 (by decide)
  have h18 : Entails.eval a c103 := h 102 (by decide)
  have h19 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8486 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8486 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c1232, some c1222, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8486 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8486 : lratChecker f8486 p8486 = .success := by decide +kernel
theorem unsat8486 : Unsatisfiable (PosFin 65) f8486 := by
  apply lratCheckerSound f8486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8486
  · intro a ha; simp [p8486] at ha; subst a; trivial
  · exact checked8486
theorem derived8486 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8486 := by
  apply localUnsat_implies_entails f8486 [c8380, c1232, c1222] c8486 unsat8486 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c1232 := h 1231 (by decide)
  have h2 : Entails.eval a c1222 := h 1221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8487 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨60, by decide⟩, false), (⟨49, by decide⟩, false), (⟨11, by decide⟩, true), (⟨54, by decide⟩, true), (⟨64, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8487 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4910, some c4894, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8487 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8487 : lratChecker f8487 p8487 = .success := by decide +kernel
theorem unsat8487 : Unsatisfiable (PosFin 65) f8487 := by
  apply lratCheckerSound f8487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8487
  · intro a ha; simp [p8487] at ha; subst a; trivial
  · exact checked8487
theorem derived8487 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8487 := by
  apply localUnsat_implies_entails f8487 [c4910, c4894] c8487 unsat8487 (by rfl) a
  have h0 : Entails.eval a c4910 := h 4909 (by decide)
  have h1 : Entails.eval a c4894 := h 4893 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8488 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨19, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8488 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5522, some c5516, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8488 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8488 : lratChecker f8488 p8488 = .success := by decide +kernel
theorem unsat8488 : Unsatisfiable (PosFin 65) f8488 := by
  apply lratCheckerSound f8488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8488
  · intro a ha; simp [p8488] at ha; subst a; trivial
  · exact checked8488
theorem derived8488 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8488 := by
  apply localUnsat_implies_entails f8488 [c5522, c5516] c8488 unsat8488 (by rfl) a
  have h0 : Entails.eval a c5522 := h 5521 (by decide)
  have h1 : Entails.eval a c5516 := h 5515 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8489 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8489 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8424, some c654, some c8426, some c8435, some c8436, some c681, some c685, some c690, some c8488, some c5985, some c5899, some c5904, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8489 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8489 : lratChecker f8489 p8489 = .success := by decide +kernel
theorem unsat8489 : Unsatisfiable (PosFin 65) f8489 := by
  apply lratCheckerSound f8489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8489
  · intro a ha; simp [p8489] at ha; subst a; trivial
  · exact checked8489
theorem derived8489 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8489 := by
  apply localUnsat_implies_entails f8489 [c8424, c654, c8426, c8435, c8436, c681, c685, c690, c8488, c5985, c5899, c5904] c8489 unsat8489 (by rfl) a
  have h0 : Entails.eval a c8424 := derived8424 a h
  have h1 : Entails.eval a c654 := h 653 (by decide)
  have h2 : Entails.eval a c8426 := derived8426 a h
  have h3 : Entails.eval a c8435 := derived8435 a h
  have h4 : Entails.eval a c8436 := derived8436 a h
  have h5 : Entails.eval a c681 := h 680 (by decide)
  have h6 : Entails.eval a c685 := h 684 (by decide)
  have h7 : Entails.eval a c690 := h 689 (by decide)
  have h8 : Entails.eval a c8488 := derived8488 a h
  have h9 : Entails.eval a c5985 := h 5984 (by decide)
  have h10 : Entails.eval a c5899 := h 5898 (by decide)
  have h11 : Entails.eval a c5904 := h 5903 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8490 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8490 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c670, some c678, some c8445, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8490 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8490 : lratChecker f8490 p8490 = .success := by decide +kernel
theorem unsat8490 : Unsatisfiable (PosFin 65) f8490 := by
  apply lratCheckerSound f8490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8490
  · intro a ha; simp [p8490] at ha; subst a; trivial
  · exact checked8490
theorem derived8490 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8490 := by
  apply localUnsat_implies_entails f8490 [c670, c678, c8445] c8490 unsat8490 (by rfl) a
  have h0 : Entails.eval a c670 := h 669 (by decide)
  have h1 : Entails.eval a c678 := h 677 (by decide)
  have h2 : Entails.eval a c8445 := derived8445 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8491 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8491 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8470, some c8489, some c8431, some c8426, some c662, some c8490, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8491 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8491 : lratChecker f8491 p8491 = .success := by decide +kernel
theorem unsat8491 : Unsatisfiable (PosFin 65) f8491 := by
  apply lratCheckerSound f8491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8491
  · intro a ha; simp [p8491] at ha; subst a; trivial
  · exact checked8491
theorem derived8491 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8491 := by
  apply localUnsat_implies_entails f8491 [c8470, c8489, c8431, c8426, c662, c8490] c8491 unsat8491 (by rfl) a
  have h0 : Entails.eval a c8470 := derived8470 a h
  have h1 : Entails.eval a c8489 := derived8489 a h
  have h2 : Entails.eval a c8431 := derived8431 a h
  have h3 : Entails.eval a c8426 := derived8426 a h
  have h4 : Entails.eval a c662 := h 661 (by decide)
  have h5 : Entails.eval a c8490 := derived8490 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8492 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨63, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8492 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1239, some c1222, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8492 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8492 : lratChecker f8492 p8492 = .success := by decide +kernel
theorem unsat8492 : Unsatisfiable (PosFin 65) f8492 := by
  apply lratCheckerSound f8492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8492
  · intro a ha; simp [p8492] at ha; subst a; trivial
  · exact checked8492
theorem derived8492 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8492 := by
  apply localUnsat_implies_entails f8492 [c1239, c1222] c8492 unsat8492 (by rfl) a
  have h0 : Entails.eval a c1239 := h 1238 (by decide)
  have h1 : Entails.eval a c1222 := h 1221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8493 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨32, by decide⟩, false), (⟨24, by decide⟩, false), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8493 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5873, some c5909, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p8493 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8493 : lratChecker f8493 p8493 = .success := by decide +kernel
theorem unsat8493 : Unsatisfiable (PosFin 65) f8493 := by
  apply lratCheckerSound f8493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8493
  · intro a ha; simp [p8493] at ha; subst a; trivial
  · exact checked8493
theorem derived8493 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8493 := by
  apply localUnsat_implies_entails f8493 [c5873, c5909] c8493 unsat8493 (by rfl) a
  have h0 : Entails.eval a c5873 := h 5872 (by decide)
  have h1 : Entails.eval a c5909 := h 5908 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8494 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8494 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8426, some c8490, some c653, some c654, some c702, some c8435, some c8436, some c681, some c664, some c655, some c705, some c703, some c8493, some c5577, some c5709, some c5851, some c5910, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8494 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8494 : lratChecker f8494 p8494 = .success := by decide +kernel
theorem unsat8494 : Unsatisfiable (PosFin 65) f8494 := by
  apply lratCheckerSound f8494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8494
  · intro a ha; simp [p8494] at ha; subst a; trivial
  · exact checked8494
theorem derived8494 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8494 := by
  apply localUnsat_implies_entails f8494 [c8426, c8490, c653, c654, c702, c8435, c8436, c681, c664, c655, c705, c703, c8493, c5577, c5709, c5851, c5910] c8494 unsat8494 (by rfl) a
  have h0 : Entails.eval a c8426 := derived8426 a h
  have h1 : Entails.eval a c8490 := derived8490 a h
  have h2 : Entails.eval a c653 := h 652 (by decide)
  have h3 : Entails.eval a c654 := h 653 (by decide)
  have h4 : Entails.eval a c702 := h 701 (by decide)
  have h5 : Entails.eval a c8435 := derived8435 a h
  have h6 : Entails.eval a c8436 := derived8436 a h
  have h7 : Entails.eval a c681 := h 680 (by decide)
  have h8 : Entails.eval a c664 := h 663 (by decide)
  have h9 : Entails.eval a c655 := h 654 (by decide)
  have h10 : Entails.eval a c705 := h 704 (by decide)
  have h11 : Entails.eval a c703 := h 702 (by decide)
  have h12 : Entails.eval a c8493 := derived8493 a h
  have h13 : Entails.eval a c5577 := h 5576 (by decide)
  have h14 : Entails.eval a c5709 := h 5708 (by decide)
  have h15 : Entails.eval a c5851 := h 5850 (by decide)
  have h16 : Entails.eval a c5910 := h 5909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8495 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨63, by decide⟩, true), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8495 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8469, some c8494, some c5513, some c5553, some c5543, some c5948, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8495 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8495 : lratChecker f8495 p8495 = .success := by decide +kernel
theorem unsat8495 : Unsatisfiable (PosFin 65) f8495 := by
  apply lratCheckerSound f8495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8495
  · intro a ha; simp [p8495] at ha; subst a; trivial
  · exact checked8495
theorem derived8495 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8495 := by
  apply localUnsat_implies_entails f8495 [c8469, c8494, c5513, c5553, c5543, c5948] c8495 unsat8495 (by rfl) a
  have h0 : Entails.eval a c8469 := derived8469 a h
  have h1 : Entails.eval a c8494 := derived8494 a h
  have h2 : Entails.eval a c5513 := h 5512 (by decide)
  have h3 : Entails.eval a c5553 := h 5552 (by decide)
  have h4 : Entails.eval a c5543 := h 5542 (by decide)
  have h5 : Entails.eval a c5948 := h 5947 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8496 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8496 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8426, some c8490, some c662, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8496 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8496 : lratChecker f8496 p8496 = .success := by decide +kernel
theorem unsat8496 : Unsatisfiable (PosFin 65) f8496 := by
  apply lratCheckerSound f8496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8496
  · intro a ha; simp [p8496] at ha; subst a; trivial
  · exact checked8496
theorem derived8496 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8496 := by
  apply localUnsat_implies_entails f8496 [c8426, c8490, c662] c8496 unsat8496 (by rfl) a
  have h0 : Entails.eval a c8426 := derived8426 a h
  have h1 : Entails.eval a c8490 := derived8490 a h
  have h2 : Entails.eval a c662 := h 661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8497 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8497 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8485, some c8380, some c8421, some c8491, some c8492, some c8495, some c8496, some c4897, some c229, some c2735, some c5769, some c4720, some c5610, some c887, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8497 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8497 : lratChecker f8497 p8497 = .success := by decide +kernel
theorem unsat8497 : Unsatisfiable (PosFin 65) f8497 := by
  apply lratCheckerSound f8497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8497
  · intro a ha; simp [p8497] at ha; subst a; trivial
  · exact checked8497
theorem derived8497 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8497 := by
  apply localUnsat_implies_entails f8497 [c8485, c8380, c8421, c8491, c8492, c8495, c8496, c4897, c229, c2735, c5769, c4720, c5610, c887] c8497 unsat8497 (by rfl) a
  have h0 : Entails.eval a c8485 := derived8485 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8491 := derived8491 a h
  have h4 : Entails.eval a c8492 := derived8492 a h
  have h5 : Entails.eval a c8495 := derived8495 a h
  have h6 : Entails.eval a c8496 := derived8496 a h
  have h7 : Entails.eval a c4897 := h 4896 (by decide)
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c2735 := h 2734 (by decide)
  have h10 : Entails.eval a c5769 := h 5768 (by decide)
  have h11 : Entails.eval a c4720 := h 4719 (by decide)
  have h12 : Entails.eval a c5610 := h 5609 (by decide)
  have h13 : Entails.eval a c887 := h 886 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8498 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨24, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8498 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5977, some c625, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8498 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8498 : lratChecker f8498 p8498 = .success := by decide +kernel
theorem unsat8498 : Unsatisfiable (PosFin 65) f8498 := by
  apply lratCheckerSound f8498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8498
  · intro a ha; simp [p8498] at ha; subst a; trivial
  · exact checked8498
theorem derived8498 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8498 := by
  apply localUnsat_implies_entails f8498 [c5977, c625] c8498 unsat8498 (by rfl) a
  have h0 : Entails.eval a c5977 := h 5976 (by decide)
  have h1 : Entails.eval a c625 := h 624 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8499 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨63, by decide⟩, false), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8499 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8426, some c8490, some c654, some c702, some c8436, some c681, some c664, some c8498, some c5577, some c5583, some c5867, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8499 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8499 : lratChecker f8499 p8499 = .success := by decide +kernel
theorem unsat8499 : Unsatisfiable (PosFin 65) f8499 := by
  apply lratCheckerSound f8499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8499
  · intro a ha; simp [p8499] at ha; subst a; trivial
  · exact checked8499
theorem derived8499 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8499 := by
  apply localUnsat_implies_entails f8499 [c8426, c8490, c654, c702, c8436, c681, c664, c8498, c5577, c5583, c5867] c8499 unsat8499 (by rfl) a
  have h0 : Entails.eval a c8426 := derived8426 a h
  have h1 : Entails.eval a c8490 := derived8490 a h
  have h2 : Entails.eval a c654 := h 653 (by decide)
  have h3 : Entails.eval a c702 := h 701 (by decide)
  have h4 : Entails.eval a c8436 := derived8436 a h
  have h5 : Entails.eval a c681 := h 680 (by decide)
  have h6 : Entails.eval a c664 := h 663 (by decide)
  have h7 : Entails.eval a c8498 := derived8498 a h
  have h8 : Entails.eval a c5577 := h 5576 (by decide)
  have h9 : Entails.eval a c5583 := h 5582 (by decide)
  have h10 : Entails.eval a c5867 := h 5866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8500 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨63, by decide⟩, false), (⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8500 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8499, some c5513, some c5553, some c5543, some c5945, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8500 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8500 : lratChecker f8500 p8500 = .success := by decide +kernel
theorem unsat8500 : Unsatisfiable (PosFin 65) f8500 := by
  apply lratCheckerSound f8500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8500
  · intro a ha; simp [p8500] at ha; subst a; trivial
  · exact checked8500
theorem derived8500 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8500 := by
  apply localUnsat_implies_entails f8500 [c8499, c5513, c5553, c5543, c5945] c8500 unsat8500 (by rfl) a
  have h0 : Entails.eval a c8499 := derived8499 a h
  have h1 : Entails.eval a c5513 := h 5512 (by decide)
  have h2 : Entails.eval a c5553 := h 5552 (by decide)
  have h3 : Entails.eval a c5543 := h 5542 (by decide)
  have h4 : Entails.eval a c5945 := h 5944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8501 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, true), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8501 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5890, some c5945, some c5775, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8501 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8501 : lratChecker f8501 p8501 = .success := by decide +kernel
theorem unsat8501 : Unsatisfiable (PosFin 65) f8501 := by
  apply lratCheckerSound f8501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8501
  · intro a ha; simp [p8501] at ha; subst a; trivial
  · exact checked8501
theorem derived8501 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8501 := by
  apply localUnsat_implies_entails f8501 [c5890, c5945, c5775] c8501 unsat8501 (by rfl) a
  have h0 : Entails.eval a c5890 := h 5889 (by decide)
  have h1 : Entails.eval a c5945 := h 5944 (by decide)
  have h2 : Entails.eval a c5775 := h 5774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8502 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨63, by decide⟩, false), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8502 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8500, some c8496, some c8501, some c5726, some c5651, some c5788, some c6238, some c6213, some c5833, some c6012, some c6065, some c6039, some c6161, some c1253, some c1181, some c4720, some c887, some c884, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8502 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8502 : lratChecker f8502 p8502 = .success := by decide +kernel
theorem unsat8502 : Unsatisfiable (PosFin 65) f8502 := by
  apply lratCheckerSound f8502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8502
  · intro a ha; simp [p8502] at ha; subst a; trivial
  · exact checked8502
theorem derived8502 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8502 := by
  apply localUnsat_implies_entails f8502 [c8380, c8500, c8496, c8501, c5726, c5651, c5788, c6238, c6213, c5833, c6012, c6065, c6039, c6161, c1253, c1181, c4720, c887, c884] c8502 unsat8502 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8500 := derived8500 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c8501 := derived8501 a h
  have h4 : Entails.eval a c5726 := h 5725 (by decide)
  have h5 : Entails.eval a c5651 := h 5650 (by decide)
  have h6 : Entails.eval a c5788 := h 5787 (by decide)
  have h7 : Entails.eval a c6238 := h 6237 (by decide)
  have h8 : Entails.eval a c6213 := h 6212 (by decide)
  have h9 : Entails.eval a c5833 := h 5832 (by decide)
  have h10 : Entails.eval a c6012 := h 6011 (by decide)
  have h11 : Entails.eval a c6065 := h 6064 (by decide)
  have h12 : Entails.eval a c6039 := h 6038 (by decide)
  have h13 : Entails.eval a c6161 := h 6160 (by decide)
  have h14 : Entails.eval a c1253 := h 1252 (by decide)
  have h15 : Entails.eval a c1181 := h 1180 (by decide)
  have h16 : Entails.eval a c4720 := h 4719 (by decide)
  have h17 : Entails.eval a c887 := h 886 (by decide)
  have h18 : Entails.eval a c884 := h 883 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8503 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8503 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8485, some c8380, some c8497, some c8500, some c8496, some c8502, some c5813, some c5782, some c5651, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8503 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8503 : lratChecker f8503 p8503 = .success := by decide +kernel
theorem unsat8503 : Unsatisfiable (PosFin 65) f8503 := by
  apply lratCheckerSound f8503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8503
  · intro a ha; simp [p8503] at ha; subst a; trivial
  · exact checked8503
theorem derived8503 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8503 := by
  apply localUnsat_implies_entails f8503 [c8485, c8380, c8497, c8500, c8496, c8502, c5813, c5782, c5651] c8503 unsat8503 (by rfl) a
  have h0 : Entails.eval a c8485 := derived8485 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c8497 := derived8497 a h
  have h3 : Entails.eval a c8500 := derived8500 a h
  have h4 : Entails.eval a c8496 := derived8496 a h
  have h5 : Entails.eval a c8502 := derived8502 a h
  have h6 : Entails.eval a c5813 := h 5812 (by decide)
  have h7 : Entails.eval a c5782 := h 5781 (by decide)
  have h8 : Entails.eval a c5651 := h 5650 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8504 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8504 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8438, some c8435, some c8436, some c690, some c692, some c675, some c667, some c703, some c655, some c698, some c671, some c8498, some c5596, some c5599, some c5864, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8504 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8504 : lratChecker f8504 p8504 = .success := by decide +kernel
theorem unsat8504 : Unsatisfiable (PosFin 65) f8504 := by
  apply lratCheckerSound f8504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8504
  · intro a ha; simp [p8504] at ha; subst a; trivial
  · exact checked8504
theorem derived8504 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8504 := by
  apply localUnsat_implies_entails f8504 [c8438, c8435, c8436, c690, c692, c675, c667, c703, c655, c698, c671, c8498, c5596, c5599, c5864] c8504 unsat8504 (by rfl) a
  have h0 : Entails.eval a c8438 := derived8438 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8436 := derived8436 a h
  have h3 : Entails.eval a c690 := h 689 (by decide)
  have h4 : Entails.eval a c692 := h 691 (by decide)
  have h5 : Entails.eval a c675 := h 674 (by decide)
  have h6 : Entails.eval a c667 := h 666 (by decide)
  have h7 : Entails.eval a c703 := h 702 (by decide)
  have h8 : Entails.eval a c655 := h 654 (by decide)
  have h9 : Entails.eval a c698 := h 697 (by decide)
  have h10 : Entails.eval a c671 := h 670 (by decide)
  have h11 : Entails.eval a c8498 := derived8498 a h
  have h12 : Entails.eval a c5596 := h 5595 (by decide)
  have h13 : Entails.eval a c5599 := h 5598 (by decide)
  have h14 : Entails.eval a c5864 := h 5863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8505 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8505 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8435, some c8445, some c690, some c692, some c675, some c703, some c662, some c698, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8505 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8505 : lratChecker f8505 p8505 = .success := by decide +kernel
theorem unsat8505 : Unsatisfiable (PosFin 65) f8505 := by
  apply lratCheckerSound f8505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8505
  · intro a ha; simp [p8505] at ha; subst a; trivial
  · exact checked8505
theorem derived8505 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8505 := by
  apply localUnsat_implies_entails f8505 [c8435, c8445, c690, c692, c675, c703, c662, c698] c8505 unsat8505 (by rfl) a
  have h0 : Entails.eval a c8435 := derived8435 a h
  have h1 : Entails.eval a c8445 := derived8445 a h
  have h2 : Entails.eval a c690 := h 689 (by decide)
  have h3 : Entails.eval a c692 := h 691 (by decide)
  have h4 : Entails.eval a c675 := h 674 (by decide)
  have h5 : Entails.eval a c703 := h 702 (by decide)
  have h6 : Entails.eval a c662 := h 661 (by decide)
  have h7 : Entails.eval a c698 := h 697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8506 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨24, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8506 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c663, some c666, some c698, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8506 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8506 : lratChecker f8506 p8506 = .success := by decide +kernel
theorem unsat8506 : Unsatisfiable (PosFin 65) f8506 := by
  apply lratCheckerSound f8506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8506
  · intro a ha; simp [p8506] at ha; subst a; trivial
  · exact checked8506
theorem derived8506 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8506 := by
  apply localUnsat_implies_entails f8506 [c663, c666, c698] c8506 unsat8506 (by rfl) a
  have h0 : Entails.eval a c663 := h 662 (by decide)
  have h1 : Entails.eval a c666 := h 665 (by decide)
  have h2 : Entails.eval a c698 := h 697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8507 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8507 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5871, some c5873, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p8507 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8507 : lratChecker f8507 p8507 = .success := by decide +kernel
theorem unsat8507 : Unsatisfiable (PosFin 65) f8507 := by
  apply lratCheckerSound f8507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8507
  · intro a ha; simp [p8507] at ha; subst a; trivial
  · exact checked8507
theorem derived8507 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8507 := by
  apply localUnsat_implies_entails f8507 [c5871, c5873] c8507 unsat8507 (by rfl) a
  have h0 : Entails.eval a c5871 := h 5870 (by decide)
  have h1 : Entails.eval a c5873 := h 5872 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8508 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8508 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5433, some c5450, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8508 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8508 : lratChecker f8508 p8508 = .success := by decide +kernel
theorem unsat8508 : Unsatisfiable (PosFin 65) f8508 := by
  apply lratCheckerSound f8508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8508
  · intro a ha; simp [p8508] at ha; subst a; trivial
  · exact checked8508
theorem derived8508 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8508 := by
  apply localUnsat_implies_entails f8508 [c5433, c5450] c8508 unsat8508 (by rfl) a
  have h0 : Entails.eval a c5433 := h 5432 (by decide)
  have h1 : Entails.eval a c5450 := h 5449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8509 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨36, by decide⟩, true), (⟨28, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8509 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c12, some c5271, some c5272, some c713, some c715, some c711, some c108, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8509 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8509 : lratChecker f8509 p8509 = .success := by decide +kernel
theorem unsat8509 : Unsatisfiable (PosFin 65) f8509 := by
  apply lratCheckerSound f8509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8509
  · intro a ha; simp [p8509] at ha; subst a; trivial
  · exact checked8509
theorem derived8509 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8509 := by
  apply localUnsat_implies_entails f8509 [c12, c5271, c5272, c713, c715, c711, c108] c8509 unsat8509 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c5271 := h 5270 (by decide)
  have h2 : Entails.eval a c5272 := h 5271 (by decide)
  have h3 : Entails.eval a c713 := h 712 (by decide)
  have h4 : Entails.eval a c715 := h 714 (by decide)
  have h5 : Entails.eval a c711 := h 710 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8510 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨24, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8510 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c667, some c668, some c691, some c699, some c694, some c686, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8510 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8510 : lratChecker f8510 p8510 = .success := by decide +kernel
theorem unsat8510 : Unsatisfiable (PosFin 65) f8510 := by
  apply lratCheckerSound f8510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8510
  · intro a ha; simp [p8510] at ha; subst a; trivial
  · exact checked8510
theorem derived8510 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8510 := by
  apply localUnsat_implies_entails f8510 [c667, c668, c691, c699, c694, c686] c8510 unsat8510 (by rfl) a
  have h0 : Entails.eval a c667 := h 666 (by decide)
  have h1 : Entails.eval a c668 := h 667 (by decide)
  have h2 : Entails.eval a c691 := h 690 (by decide)
  have h3 : Entails.eval a c699 := h 698 (by decide)
  have h4 : Entails.eval a c694 := h 693 (by decide)
  have h5 : Entails.eval a c686 := h 685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8511 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8511 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c4864, some c1124, some c4428, some c231, some c239, some c209, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8511 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8511 : lratChecker f8511 p8511 = .success := by decide +kernel
theorem unsat8511 : Unsatisfiable (PosFin 65) f8511 := by
  apply lratCheckerSound f8511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8511
  · intro a ha; simp [p8511] at ha; subst a; trivial
  · exact checked8511
theorem derived8511 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8511 := by
  apply localUnsat_implies_entails f8511 [c8380, c4864, c1124, c4428, c231, c239, c209] c8511 unsat8511 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c4864 := h 4863 (by decide)
  have h2 : Entails.eval a c1124 := h 1123 (by decide)
  have h3 : Entails.eval a c4428 := h 4427 (by decide)
  have h4 : Entails.eval a c231 := h 230 (by decide)
  have h5 : Entails.eval a c239 := h 238 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8512 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨54, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8512 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c163, some c5467, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8512 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8512 : lratChecker f8512 p8512 = .success := by decide +kernel
theorem unsat8512 : Unsatisfiable (PosFin 65) f8512 := by
  apply lratCheckerSound f8512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8512
  · intro a ha; simp [p8512] at ha; subst a; trivial
  · exact checked8512
theorem derived8512 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8512 := by
  apply localUnsat_implies_entails f8512 [c163, c5467] c8512 unsat8512 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c5467 := h 5466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8513 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨60, by decide⟩, false), (⟨36, by decide⟩, true), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨57, by decide⟩, false), (⟨19, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8513 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c676, some c688, some c691, some c8505, some c8507, some c8509, some c8508, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8513 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8513 : lratChecker f8513 p8513 = .success := by decide +kernel
theorem unsat8513 : Unsatisfiable (PosFin 65) f8513 := by
  apply lratCheckerSound f8513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8513
  · intro a ha; simp [p8513] at ha; subst a; trivial
  · exact checked8513
theorem derived8513 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8513 := by
  apply localUnsat_implies_entails f8513 [c676, c688, c691, c8505, c8507, c8509, c8508] c8513 unsat8513 (by rfl) a
  have h0 : Entails.eval a c676 := h 675 (by decide)
  have h1 : Entails.eval a c688 := h 687 (by decide)
  have h2 : Entails.eval a c691 := h 690 (by decide)
  have h3 : Entails.eval a c8505 := derived8505 a h
  have h4 : Entails.eval a c8507 := derived8507 a h
  have h5 : Entails.eval a c8509 := derived8509 a h
  have h6 : Entails.eval a c8508 := derived8508 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8514 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8514 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5683, some c5638, some c5762, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8514 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8514 : lratChecker f8514 p8514 = .success := by decide +kernel
theorem unsat8514 : Unsatisfiable (PosFin 65) f8514 := by
  apply lratCheckerSound f8514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8514
  · intro a ha; simp [p8514] at ha; subst a; trivial
  · exact checked8514
theorem derived8514 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8514 := by
  apply localUnsat_implies_entails f8514 [c5683, c5638, c5762] c8514 unsat8514 (by rfl) a
  have h0 : Entails.eval a c5683 := h 5682 (by decide)
  have h1 : Entails.eval a c5638 := h 5637 (by decide)
  have h2 : Entails.eval a c5762 := h 5761 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8515 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8515 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5945, some c5968, some c5663, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p8515 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8515 : lratChecker f8515 p8515 = .success := by decide +kernel
theorem unsat8515 : Unsatisfiable (PosFin 65) f8515 := by
  apply lratCheckerSound f8515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8515
  · intro a ha; simp [p8515] at ha; subst a; trivial
  · exact checked8515
theorem derived8515 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8515 := by
  apply localUnsat_implies_entails f8515 [c5945, c5968, c5663] c8515 unsat8515 (by rfl) a
  have h0 : Entails.eval a c5945 := h 5944 (by decide)
  have h1 : Entails.eval a c5968 := h 5967 (by decide)
  have h2 : Entails.eval a c5663 := h 5662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8516 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨64, by decide⟩, true), (⟨19, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8516 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8514, some c8515, some c5573, some c5594, some c5746, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p8516 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8516 : lratChecker f8516 p8516 = .success := by decide +kernel
theorem unsat8516 : Unsatisfiable (PosFin 65) f8516 := by
  apply lratCheckerSound f8516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8516
  · intro a ha; simp [p8516] at ha; subst a; trivial
  · exact checked8516
theorem derived8516 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8516 := by
  apply localUnsat_implies_entails f8516 [c8514, c8515, c5573, c5594, c5746] c8516 unsat8516 (by rfl) a
  have h0 : Entails.eval a c8514 := derived8514 a h
  have h1 : Entails.eval a c8515 := derived8515 a h
  have h2 : Entails.eval a c5573 := h 5572 (by decide)
  have h3 : Entails.eval a c5594 := h 5593 (by decide)
  have h4 : Entails.eval a c5746 := h 5745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8517 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8517 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8504, some c8516, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8517 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8517 : lratChecker f8517 p8517 = .success := by decide +kernel
theorem unsat8517 : Unsatisfiable (PosFin 65) f8517 := by
  apply lratCheckerSound f8517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8517
  · intro a ha; simp [p8517] at ha; subst a; trivial
  · exact checked8517
theorem derived8517 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8517 := by
  apply localUnsat_implies_entails f8517 [c8504, c8516] c8517 unsat8517 (by rfl) a
  have h0 : Entails.eval a c8504 := derived8504 a h
  have h1 : Entails.eval a c8516 := derived8516 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8518 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8518 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8485, some c8503, some c8517, some c8421, some c662, some c661, some c685, some c692, some c667, some c697, some c1178, some c8511, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8518 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8518 : lratChecker f8518 p8518 = .success := by decide +kernel
theorem unsat8518 : Unsatisfiable (PosFin 65) f8518 := by
  apply lratCheckerSound f8518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8518
  · intro a ha; simp [p8518] at ha; subst a; trivial
  · exact checked8518
theorem derived8518 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8518 := by
  apply localUnsat_implies_entails f8518 [c8380, c8485, c8503, c8517, c8421, c662, c661, c685, c692, c667, c697, c1178, c8511] c8518 unsat8518 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8485 := derived8485 a h
  have h2 : Entails.eval a c8503 := derived8503 a h
  have h3 : Entails.eval a c8517 := derived8517 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c662 := h 661 (by decide)
  have h6 : Entails.eval a c661 := h 660 (by decide)
  have h7 : Entails.eval a c685 := h 684 (by decide)
  have h8 : Entails.eval a c692 := h 691 (by decide)
  have h9 : Entails.eval a c667 := h 666 (by decide)
  have h10 : Entails.eval a c697 := h 696 (by decide)
  have h11 : Entails.eval a c1178 := h 1177 (by decide)
  have h12 : Entails.eval a c8511 := derived8511 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8519 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8519 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8503, some c8380, some c8485, some c8517, some c8505, some c8518, some c8506, some c8510, some c685, some c683, some c676, some c677, some c8512, some c698, some c688, some c691, some c8391, some c8509, some c8513, some c179, some c5355, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8519 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8519 : lratChecker f8519 p8519 = .success := by decide +kernel
theorem unsat8519 : Unsatisfiable (PosFin 65) f8519 := by
  apply lratCheckerSound f8519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8519
  · intro a ha; simp [p8519] at ha; subst a; trivial
  · exact checked8519
theorem derived8519 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8519 := by
  apply localUnsat_implies_entails f8519 [c8503, c8380, c8485, c8517, c8505, c8518, c8506, c8510, c685, c683, c676, c677, c8512, c698, c688, c691, c8391, c8509, c8513, c179, c5355] c8519 unsat8519 (by rfl) a
  have h0 : Entails.eval a c8503 := derived8503 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c8485 := derived8485 a h
  have h3 : Entails.eval a c8517 := derived8517 a h
  have h4 : Entails.eval a c8505 := derived8505 a h
  have h5 : Entails.eval a c8518 := derived8518 a h
  have h6 : Entails.eval a c8506 := derived8506 a h
  have h7 : Entails.eval a c8510 := derived8510 a h
  have h8 : Entails.eval a c685 := h 684 (by decide)
  have h9 : Entails.eval a c683 := h 682 (by decide)
  have h10 : Entails.eval a c676 := h 675 (by decide)
  have h11 : Entails.eval a c677 := h 676 (by decide)
  have h12 : Entails.eval a c8512 := derived8512 a h
  have h13 : Entails.eval a c698 := h 697 (by decide)
  have h14 : Entails.eval a c688 := h 687 (by decide)
  have h15 : Entails.eval a c691 := h 690 (by decide)
  have h16 : Entails.eval a c8391 := derived8391 a h
  have h17 : Entails.eval a c8509 := derived8509 a h
  have h18 : Entails.eval a c8513 := derived8513 a h
  have h19 : Entails.eval a c179 := h 178 (by decide)
  have h20 : Entails.eval a c5355 := h 5354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8520 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8520 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c662, some c661, some c685, some c692, some c668, some c658, some c657, some c627, some c6019, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8520 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8520 : lratChecker f8520 p8520 = .success := by decide +kernel
theorem unsat8520 : Unsatisfiable (PosFin 65) f8520 := by
  apply lratCheckerSound f8520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8520
  · intro a ha; simp [p8520] at ha; subst a; trivial
  · exact checked8520
theorem derived8520 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8520 := by
  apply localUnsat_implies_entails f8520 [c662, c661, c685, c692, c668, c658, c657, c627, c6019] c8520 unsat8520 (by rfl) a
  have h0 : Entails.eval a c662 := h 661 (by decide)
  have h1 : Entails.eval a c661 := h 660 (by decide)
  have h2 : Entails.eval a c685 := h 684 (by decide)
  have h3 : Entails.eval a c692 := h 691 (by decide)
  have h4 : Entails.eval a c668 := h 667 (by decide)
  have h5 : Entails.eval a c658 := h 657 (by decide)
  have h6 : Entails.eval a c657 := h 656 (by decide)
  have h7 : Entails.eval a c627 := h 626 (by decide)
  have h8 : Entails.eval a c6019 := h 6018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8521 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8521 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8520, some c8506, some c8510, some c685, some c676, some c677, some c631, some c6019, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8521 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8521 : lratChecker f8521 p8521 = .success := by decide +kernel
theorem unsat8521 : Unsatisfiable (PosFin 65) f8521 := by
  apply lratCheckerSound f8521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8521
  · intro a ha; simp [p8521] at ha; subst a; trivial
  · exact checked8521
theorem derived8521 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8521 := by
  apply localUnsat_implies_entails f8521 [c8520, c8506, c8510, c685, c676, c677, c631, c6019] c8521 unsat8521 (by rfl) a
  have h0 : Entails.eval a c8520 := derived8520 a h
  have h1 : Entails.eval a c8506 := derived8506 a h
  have h2 : Entails.eval a c8510 := derived8510 a h
  have h3 : Entails.eval a c685 := h 684 (by decide)
  have h4 : Entails.eval a c676 := h 675 (by decide)
  have h5 : Entails.eval a c677 := h 676 (by decide)
  have h6 : Entails.eval a c631 := h 630 (by decide)
  have h7 : Entails.eval a c6019 := h 6018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8522 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8522 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8485, some c8503, some c8517, some c8519, some c8521, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8522 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8522 : lratChecker f8522 p8522 = .success := by decide +kernel
theorem unsat8522 : Unsatisfiable (PosFin 65) f8522 := by
  apply lratCheckerSound f8522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8522
  · intro a ha; simp [p8522] at ha; subst a; trivial
  · exact checked8522
theorem derived8522 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8522 := by
  apply localUnsat_implies_entails f8522 [c8380, c8485, c8503, c8517, c8519, c8521] c8522 unsat8522 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8485 := derived8485 a h
  have h2 : Entails.eval a c8503 := derived8503 a h
  have h3 : Entails.eval a c8517 := derived8517 a h
  have h4 : Entails.eval a c8519 := derived8519 a h
  have h5 : Entails.eval a c8521 := derived8521 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8523 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8523 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8485, some c8503, some c8517, some c8522, some c29, some c16, some c6559, some c6577, some c6594, some c7083, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8523 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8523 : lratChecker f8523 p8523 = .success := by decide +kernel
theorem unsat8523 : Unsatisfiable (PosFin 65) f8523 := by
  apply lratCheckerSound f8523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8523
  · intro a ha; simp [p8523] at ha; subst a; trivial
  · exact checked8523
theorem derived8523 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8523 := by
  apply localUnsat_implies_entails f8523 [c8380, c8485, c8503, c8517, c8522, c29, c16, c6559, c6577, c6594, c7083] c8523 unsat8523 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8485 := derived8485 a h
  have h2 : Entails.eval a c8503 := derived8503 a h
  have h3 : Entails.eval a c8517 := derived8517 a h
  have h4 : Entails.eval a c8522 := derived8522 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c6559 := h 6558 (by decide)
  have h8 : Entails.eval a c6577 := h 6576 (by decide)
  have h9 : Entails.eval a c6594 := h 6593 (by decide)
  have h10 : Entails.eval a c7083 := h 7082 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8524 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨54, by decide⟩, false), (⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8524 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1125, some c1069, some c1179, some c4585, some c1008, some c4428, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8524 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8524 : lratChecker f8524 p8524 = .success := by decide +kernel
theorem unsat8524 : Unsatisfiable (PosFin 65) f8524 := by
  apply lratCheckerSound f8524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8524
  · intro a ha; simp [p8524] at ha; subst a; trivial
  · exact checked8524
theorem derived8524 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8524 := by
  apply localUnsat_implies_entails f8524 [c1125, c1069, c1179, c4585, c1008, c4428] c8524 unsat8524 (by rfl) a
  have h0 : Entails.eval a c1125 := h 1124 (by decide)
  have h1 : Entails.eval a c1069 := h 1068 (by decide)
  have h2 : Entails.eval a c1179 := h 1178 (by decide)
  have h3 : Entails.eval a c4585 := h 4584 (by decide)
  have h4 : Entails.eval a c1008 := h 1007 (by decide)
  have h5 : Entails.eval a c4428 := h 4427 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8525 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, true), (⟨28, by decide⟩, true), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false), (⟨24, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8525 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8524, some c5736, some c607, some c581, some c5858, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8525 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8525 : lratChecker f8525 p8525 = .success := by decide +kernel
theorem unsat8525 : Unsatisfiable (PosFin 65) f8525 := by
  apply lratCheckerSound f8525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8525
  · intro a ha; simp [p8525] at ha; subst a; trivial
  · exact checked8525
theorem derived8525 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8525 := by
  apply localUnsat_implies_entails f8525 [c8524, c5736, c607, c581, c5858] c8525 unsat8525 (by rfl) a
  have h0 : Entails.eval a c8524 := derived8524 a h
  have h1 : Entails.eval a c5736 := h 5735 (by decide)
  have h2 : Entails.eval a c607 := h 606 (by decide)
  have h3 : Entails.eval a c581 := h 580 (by decide)
  have h4 : Entails.eval a c5858 := h 5857 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8526 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨54, by decide⟩, true), (⟨29, by decide⟩, false), (⟨24, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8526 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5896, some c624, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8526 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8526 : lratChecker f8526 p8526 = .success := by decide +kernel
theorem unsat8526 : Unsatisfiable (PosFin 65) f8526 := by
  apply lratCheckerSound f8526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8526
  · intro a ha; simp [p8526] at ha; subst a; trivial
  · exact checked8526
theorem derived8526 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8526 := by
  apply localUnsat_implies_entails f8526 [c5896, c624] c8526 unsat8526 (by rfl) a
  have h0 : Entails.eval a c5896 := h 5895 (by decide)
  have h1 : Entails.eval a c624 := h 623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8527 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8527 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8523, some c8380, some c8426, some c8490, some c654, some c702, some c8435, some c8436, some c681, some c664, some c655, some c705, some c703, some c8525, some c8526, some c5596, some c607, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8527 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8527 : lratChecker f8527 p8527 = .success := by decide +kernel
theorem unsat8527 : Unsatisfiable (PosFin 65) f8527 := by
  apply lratCheckerSound f8527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8527
  · intro a ha; simp [p8527] at ha; subst a; trivial
  · exact checked8527
theorem derived8527 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8527 := by
  apply localUnsat_implies_entails f8527 [c8523, c8380, c8426, c8490, c654, c702, c8435, c8436, c681, c664, c655, c705, c703, c8525, c8526, c5596, c607] c8527 unsat8527 (by rfl) a
  have h0 : Entails.eval a c8523 := derived8523 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c8426 := derived8426 a h
  have h3 : Entails.eval a c8490 := derived8490 a h
  have h4 : Entails.eval a c654 := h 653 (by decide)
  have h5 : Entails.eval a c702 := h 701 (by decide)
  have h6 : Entails.eval a c8435 := derived8435 a h
  have h7 : Entails.eval a c8436 := derived8436 a h
  have h8 : Entails.eval a c681 := h 680 (by decide)
  have h9 : Entails.eval a c664 := h 663 (by decide)
  have h10 : Entails.eval a c655 := h 654 (by decide)
  have h11 : Entails.eval a c705 := h 704 (by decide)
  have h12 : Entails.eval a c703 := h 702 (by decide)
  have h13 : Entails.eval a c8525 := derived8525 a h
  have h14 : Entails.eval a c8526 := derived8526 a h
  have h15 : Entails.eval a c5596 := h 5595 (by decide)
  have h16 : Entails.eval a c607 := h 606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8528 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8528 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5676, some c5672, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p8528 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8528 : lratChecker f8528 p8528 = .success := by decide +kernel
theorem unsat8528 : Unsatisfiable (PosFin 65) f8528 := by
  apply lratCheckerSound f8528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8528
  · intro a ha; simp [p8528] at ha; subst a; trivial
  · exact checked8528
theorem derived8528 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8528 := by
  apply localUnsat_implies_entails f8528 [c5676, c5672] c8528 unsat8528 (by rfl) a
  have h0 : Entails.eval a c5676 := h 5675 (by decide)
  have h1 : Entails.eval a c5672 := h 5671 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8529 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8529 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c937, some c1201, some c4864, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8529 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8529 : lratChecker f8529 p8529 = .success := by decide +kernel
theorem unsat8529 : Unsatisfiable (PosFin 65) f8529 := by
  apply lratCheckerSound f8529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8529
  · intro a ha; simp [p8529] at ha; subst a; trivial
  · exact checked8529
theorem derived8529 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8529 := by
  apply localUnsat_implies_entails f8529 [c937, c1201, c4864] c8529 unsat8529 (by rfl) a
  have h0 : Entails.eval a c937 := h 936 (by decide)
  have h1 : Entails.eval a c1201 := h 1200 (by decide)
  have h2 : Entails.eval a c4864 := h 4863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8530 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨21, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8530 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6038, some c6165, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p8530 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8530 : lratChecker f8530 p8530 = .success := by decide +kernel
theorem unsat8530 : Unsatisfiable (PosFin 65) f8530 := by
  apply lratCheckerSound f8530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8530
  · intro a ha; simp [p8530] at ha; subst a; trivial
  · exact checked8530
theorem derived8530 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8530 := by
  apply localUnsat_implies_entails f8530 [c6038, c6165] c8530 unsat8530 (by rfl) a
  have h0 : Entails.eval a c6038 := h 6037 (by decide)
  have h1 : Entails.eval a c6165 := h 6164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8531 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨53, by decide⟩, false), (⟨63, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8531 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5972, some c5982, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p8531 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8531 : lratChecker f8531 p8531 = .success := by decide +kernel
theorem unsat8531 : Unsatisfiable (PosFin 65) f8531 := by
  apply lratCheckerSound f8531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8531
  · intro a ha; simp [p8531] at ha; subst a; trivial
  · exact checked8531
theorem derived8531 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8531 := by
  apply localUnsat_implies_entails f8531 [c5972, c5982] c8531 unsat8531 (by rfl) a
  have h0 : Entails.eval a c5972 := h 5971 (by decide)
  have h1 : Entails.eval a c5982 := h 5981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8532 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8532 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1178, some c4864, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8532 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8532 : lratChecker f8532 p8532 = .success := by decide +kernel
theorem unsat8532 : Unsatisfiable (PosFin 65) f8532 := by
  apply lratCheckerSound f8532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8532
  · intro a ha; simp [p8532] at ha; subst a; trivial
  · exact checked8532
theorem derived8532 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8532 := by
  apply localUnsat_implies_entails f8532 [c1178, c4864] c8532 unsat8532 (by rfl) a
  have h0 : Entails.eval a c1178 := h 1177 (by decide)
  have h1 : Entails.eval a c4864 := h 4863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8533 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨63, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8533 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5561, some c5557, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p8533 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8533 : lratChecker f8533 p8533 = .success := by decide +kernel
theorem unsat8533 : Unsatisfiable (PosFin 65) f8533 := by
  apply lratCheckerSound f8533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8533
  · intro a ha; simp [p8533] at ha; subst a; trivial
  · exact checked8533
theorem derived8533 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8533 := by
  apply localUnsat_implies_entails f8533 [c5561, c5557] c8533 unsat8533 (by rfl) a
  have h0 : Entails.eval a c5561 := h 5560 (by decide)
  have h1 : Entails.eval a c5557 := h 5556 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8534 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8534 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5635, some c5627, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8534 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8534 : lratChecker f8534 p8534 = .success := by decide +kernel
theorem unsat8534 : Unsatisfiable (PosFin 65) f8534 := by
  apply lratCheckerSound f8534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8534
  · intro a ha; simp [p8534] at ha; subst a; trivial
  · exact checked8534
theorem derived8534 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8534 := by
  apply localUnsat_implies_entails f8534 [c5635, c5627] c8534 unsat8534 (by rfl) a
  have h0 : Entails.eval a c5635 := h 5634 (by decide)
  have h1 : Entails.eval a c5627 := h 5626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8535 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨63, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8535 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8424, some c8533, some c8531, some c8528, some c8534, some c8529, some c8532, some c909, some c921, some c932, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8535 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8535 : lratChecker f8535 p8535 = .success := by decide +kernel
theorem unsat8535 : Unsatisfiable (PosFin 65) f8535 := by
  apply lratCheckerSound f8535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8535
  · intro a ha; simp [p8535] at ha; subst a; trivial
  · exact checked8535
theorem derived8535 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8535 := by
  apply localUnsat_implies_entails f8535 [c8380, c8424, c8533, c8531, c8528, c8534, c8529, c8532, c909, c921, c932] c8535 unsat8535 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8424 := derived8424 a h
  have h2 : Entails.eval a c8533 := derived8533 a h
  have h3 : Entails.eval a c8531 := derived8531 a h
  have h4 : Entails.eval a c8528 := derived8528 a h
  have h5 : Entails.eval a c8534 := derived8534 a h
  have h6 : Entails.eval a c8529 := derived8529 a h
  have h7 : Entails.eval a c8532 := derived8532 a h
  have h8 : Entails.eval a c909 := h 908 (by decide)
  have h9 : Entails.eval a c921 := h 920 (by decide)
  have h10 : Entails.eval a c932 := h 931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8536 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8536 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8527, some c8523, some c8380, some c8421, some c8484, some c8424, some c8535, some c5518, some c5520, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8536 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8536 : lratChecker f8536 p8536 = .success := by decide +kernel
theorem unsat8536 : Unsatisfiable (PosFin 65) f8536 := by
  apply lratCheckerSound f8536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8536
  · intro a ha; simp [p8536] at ha; subst a; trivial
  · exact checked8536
theorem derived8536 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8536 := by
  apply localUnsat_implies_entails f8536 [c8527, c8523, c8380, c8421, c8484, c8424, c8535, c5518, c5520] c8536 unsat8536 (by rfl) a
  have h0 : Entails.eval a c8527 := derived8527 a h
  have h1 : Entails.eval a c8523 := derived8523 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8484 := derived8484 a h
  have h5 : Entails.eval a c8424 := derived8424 a h
  have h6 : Entails.eval a c8535 := derived8535 a h
  have h7 : Entails.eval a c5518 := h 5517 (by decide)
  have h8 : Entails.eval a c5520 := h 5519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8537 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨18, by decide⟩, true), (⟨64, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8537 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5513, some c5554, some c5543, some c5946, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8537 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8537 : lratChecker f8537 p8537 = .success := by decide +kernel
theorem unsat8537 : Unsatisfiable (PosFin 65) f8537 := by
  apply lratCheckerSound f8537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8537
  · intro a ha; simp [p8537] at ha; subst a; trivial
  · exact checked8537
theorem derived8537 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8537 := by
  apply localUnsat_implies_entails f8537 [c5513, c5554, c5543, c5946] c8537 unsat8537 (by rfl) a
  have h0 : Entails.eval a c5513 := h 5512 (by decide)
  have h1 : Entails.eval a c5554 := h 5553 (by decide)
  have h2 : Entails.eval a c5543 := h 5542 (by decide)
  have h3 : Entails.eval a c5946 := h 5945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8538 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8538 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8527, some c8536, some c8537, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8538 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8538 : lratChecker f8538 p8538 = .success := by decide +kernel
theorem unsat8538 : Unsatisfiable (PosFin 65) f8538 := by
  apply lratCheckerSound f8538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8538
  · intro a ha; simp [p8538] at ha; subst a; trivial
  · exact checked8538
theorem derived8538 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8538 := by
  apply localUnsat_implies_entails f8538 [c8380, c8527, c8536, c8537] c8538 unsat8538 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8527 := derived8527 a h
  have h2 : Entails.eval a c8536 := derived8536 a h
  have h3 : Entails.eval a c8537 := derived8537 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8539 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨63, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8539 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8538, some c8496, some c8380, some c8421, some c8486, some c8429, some c4895, some c3675, some c2733, some c212, some c4490, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8539 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8539 : lratChecker f8539 p8539 = .success := by decide +kernel
theorem unsat8539 : Unsatisfiable (PosFin 65) f8539 := by
  apply lratCheckerSound f8539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8539
  · intro a ha; simp [p8539] at ha; subst a; trivial
  · exact checked8539
theorem derived8539 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8539 := by
  apply localUnsat_implies_entails f8539 [c8538, c8496, c8380, c8421, c8486, c8429, c4895, c3675, c2733, c212, c4490] c8539 unsat8539 (by rfl) a
  have h0 : Entails.eval a c8538 := derived8538 a h
  have h1 : Entails.eval a c8496 := derived8496 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8486 := derived8486 a h
  have h5 : Entails.eval a c8429 := derived8429 a h
  have h6 : Entails.eval a c4895 := h 4894 (by decide)
  have h7 : Entails.eval a c3675 := h 3674 (by decide)
  have h8 : Entails.eval a c2733 := h 2732 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c4490 := h 4489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8540 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨63, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8540 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5880, some c5886, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p8540 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8540 : lratChecker f8540 p8540 = .success := by decide +kernel
theorem unsat8540 : Unsatisfiable (PosFin 65) f8540 := by
  apply lratCheckerSound f8540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8540
  · intro a ha; simp [p8540] at ha; subst a; trivial
  · exact checked8540
theorem derived8540 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8540 := by
  apply localUnsat_implies_entails f8540 [c5880, c5886] c8540 unsat8540 (by rfl) a
  have h0 : Entails.eval a c5880 := h 5879 (by decide)
  have h1 : Entails.eval a c5886 := h 5885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8541 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8541 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8523, some c885, some c1125, some c1179, some c4701, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8541 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8541 : lratChecker f8541 p8541 = .success := by decide +kernel
theorem unsat8541 : Unsatisfiable (PosFin 65) f8541 := by
  apply lratCheckerSound f8541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8541
  · intro a ha; simp [p8541] at ha; subst a; trivial
  · exact checked8541
theorem derived8541 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8541 := by
  apply localUnsat_implies_entails f8541 [c8523, c885, c1125, c1179, c4701] c8541 unsat8541 (by rfl) a
  have h0 : Entails.eval a c8523 := derived8523 a h
  have h1 : Entails.eval a c885 := h 884 (by decide)
  have h2 : Entails.eval a c1125 := h 1124 (by decide)
  have h3 : Entails.eval a c1179 := h 1178 (by decide)
  have h4 : Entails.eval a c4701 := h 4700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8542 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8542 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6141, some c6147, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8542 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8542 : lratChecker f8542 p8542 = .success := by decide +kernel
theorem unsat8542 : Unsatisfiable (PosFin 65) f8542 := by
  apply lratCheckerSound f8542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8542
  · intro a ha; simp [p8542] at ha; subst a; trivial
  · exact checked8542
theorem derived8542 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8542 := by
  apply localUnsat_implies_entails f8542 [c6141, c6147] c8542 unsat8542 (by rfl) a
  have h0 : Entails.eval a c6141 := h 6140 (by decide)
  have h1 : Entails.eval a c6147 := h 6146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8543 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨54, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8543 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8523, some c8538, some c8496, some c8484, some c8539, some c8531, some c8380, some c8540, some c8542, some c1125, some c1179, some c4701, some c886, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8543 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8543 : lratChecker f8543 p8543 = .success := by decide +kernel
theorem unsat8543 : Unsatisfiable (PosFin 65) f8543 := by
  apply lratCheckerSound f8543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8543
  · intro a ha; simp [p8543] at ha; subst a; trivial
  · exact checked8543
theorem derived8543 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8543 := by
  apply localUnsat_implies_entails f8543 [c8523, c8538, c8496, c8484, c8539, c8531, c8380, c8540, c8542, c1125, c1179, c4701, c886] c8543 unsat8543 (by rfl) a
  have h0 : Entails.eval a c8523 := derived8523 a h
  have h1 : Entails.eval a c8538 := derived8538 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c8484 := derived8484 a h
  have h4 : Entails.eval a c8539 := derived8539 a h
  have h5 : Entails.eval a c8531 := derived8531 a h
  have h6 : Entails.eval a c8380 := derived8380 a h
  have h7 : Entails.eval a c8540 := derived8540 a h
  have h8 : Entails.eval a c8542 := derived8542 a h
  have h9 : Entails.eval a c1125 := h 1124 (by decide)
  have h10 : Entails.eval a c1179 := h 1178 (by decide)
  have h11 : Entails.eval a c4701 := h 4700 (by decide)
  have h12 : Entails.eval a c886 := h 885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8544 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8544 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c921, some c925, some c932, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8544 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8544 : lratChecker f8544 p8544 = .success := by decide +kernel
theorem unsat8544 : Unsatisfiable (PosFin 65) f8544 := by
  apply lratCheckerSound f8544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8544
  · intro a ha; simp [p8544] at ha; subst a; trivial
  · exact checked8544
theorem derived8544 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8544 := by
  apply localUnsat_implies_entails f8544 [c921, c925, c932] c8544 unsat8544 (by rfl) a
  have h0 : Entails.eval a c921 := h 920 (by decide)
  have h1 : Entails.eval a c925 := h 924 (by decide)
  have h2 : Entails.eval a c932 := h 931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8545 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨54, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8545 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8484, some c8538, some c8496, some c8523, some c8380, some c8421, some c8539, some c8531, some c8543, some c8544, some c8532, some c8542, some c1179, some c8541, some c4886, some c4867, some c4880, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8545 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8545 : lratChecker f8545 p8545 = .success := by decide +kernel
theorem unsat8545 : Unsatisfiable (PosFin 65) f8545 := by
  apply lratCheckerSound f8545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8545
  · intro a ha; simp [p8545] at ha; subst a; trivial
  · exact checked8545
theorem derived8545 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8545 := by
  apply localUnsat_implies_entails f8545 [c8484, c8538, c8496, c8523, c8380, c8421, c8539, c8531, c8543, c8544, c8532, c8542, c1179, c8541, c4886, c4867, c4880] c8545 unsat8545 (by rfl) a
  have h0 : Entails.eval a c8484 := derived8484 a h
  have h1 : Entails.eval a c8538 := derived8538 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c8523 := derived8523 a h
  have h4 : Entails.eval a c8380 := derived8380 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8539 := derived8539 a h
  have h7 : Entails.eval a c8531 := derived8531 a h
  have h8 : Entails.eval a c8543 := derived8543 a h
  have h9 : Entails.eval a c8544 := derived8544 a h
  have h10 : Entails.eval a c8532 := derived8532 a h
  have h11 : Entails.eval a c8542 := derived8542 a h
  have h12 : Entails.eval a c1179 := h 1178 (by decide)
  have h13 : Entails.eval a c8541 := derived8541 a h
  have h14 : Entails.eval a c4886 := h 4885 (by decide)
  have h15 : Entails.eval a c4867 := h 4866 (by decide)
  have h16 : Entails.eval a c4880 := h 4879 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8546 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨63, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8546 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5781, some c5650, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p8546 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8546 : lratChecker f8546 p8546 = .success := by decide +kernel
theorem unsat8546 : Unsatisfiable (PosFin 65) f8546 := by
  apply lratCheckerSound f8546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8546
  · intro a ha; simp [p8546] at ha; subst a; trivial
  · exact checked8546
theorem derived8546 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8546 := by
  apply localUnsat_implies_entails f8546 [c5781, c5650] c8546 unsat8546 (by rfl) a
  have h0 : Entails.eval a c5781 := h 5780 (by decide)
  have h1 : Entails.eval a c5650 := h 5649 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8547 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨63, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8547 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5993, some c6001, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p8547 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8547 : lratChecker f8547 p8547 = .success := by decide +kernel
theorem unsat8547 : Unsatisfiable (PosFin 65) f8547 := by
  apply lratCheckerSound f8547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8547
  · intro a ha; simp [p8547] at ha; subst a; trivial
  · exact checked8547
theorem derived8547 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8547 := by
  apply localUnsat_implies_entails f8547 [c5993, c6001] c8547 unsat8547 (by rfl) a
  have h0 : Entails.eval a c5993 := h 5992 (by decide)
  have h1 : Entails.eval a c6001 := h 6000 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8548 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨54, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8548 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8545, some c8484, some c8538, some c8496, some c8523, some c8380, some c8546, some c8540, some c8547, some c8542, some c1125, some c1179, some c4701, some c886, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8548 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8548 : lratChecker f8548 p8548 = .success := by decide +kernel
theorem unsat8548 : Unsatisfiable (PosFin 65) f8548 := by
  apply lratCheckerSound f8548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8548
  · intro a ha; simp [p8548] at ha; subst a; trivial
  · exact checked8548
theorem derived8548 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8548 := by
  apply localUnsat_implies_entails f8548 [c8545, c8484, c8538, c8496, c8523, c8380, c8546, c8540, c8547, c8542, c1125, c1179, c4701, c886] c8548 unsat8548 (by rfl) a
  have h0 : Entails.eval a c8545 := derived8545 a h
  have h1 : Entails.eval a c8484 := derived8484 a h
  have h2 : Entails.eval a c8538 := derived8538 a h
  have h3 : Entails.eval a c8496 := derived8496 a h
  have h4 : Entails.eval a c8523 := derived8523 a h
  have h5 : Entails.eval a c8380 := derived8380 a h
  have h6 : Entails.eval a c8546 := derived8546 a h
  have h7 : Entails.eval a c8540 := derived8540 a h
  have h8 : Entails.eval a c8547 := derived8547 a h
  have h9 : Entails.eval a c8542 := derived8542 a h
  have h10 : Entails.eval a c1125 := h 1124 (by decide)
  have h11 : Entails.eval a c1179 := h 1178 (by decide)
  have h12 : Entails.eval a c4701 := h 4700 (by decide)
  have h13 : Entails.eval a c886 := h 885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8549 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8549 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8538, some c8496, some c8523, some c8484, some c8545, some c8548, some c5812, some c5826, some c5818, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8549 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8549 : lratChecker f8549 p8549 = .success := by decide +kernel
theorem unsat8549 : Unsatisfiable (PosFin 65) f8549 := by
  apply lratCheckerSound f8549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8549
  · intro a ha; simp [p8549] at ha; subst a; trivial
  · exact checked8549
theorem derived8549 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8549 := by
  apply localUnsat_implies_entails f8549 [c8538, c8496, c8523, c8484, c8545, c8548, c5812, c5826, c5818] c8549 unsat8549 (by rfl) a
  have h0 : Entails.eval a c8538 := derived8538 a h
  have h1 : Entails.eval a c8496 := derived8496 a h
  have h2 : Entails.eval a c8523 := derived8523 a h
  have h3 : Entails.eval a c8484 := derived8484 a h
  have h4 : Entails.eval a c8545 := derived8545 a h
  have h5 : Entails.eval a c8548 := derived8548 a h
  have h6 : Entails.eval a c5812 := h 5811 (by decide)
  have h7 : Entails.eval a c5826 := h 5825 (by decide)
  have h8 : Entails.eval a c5818 := h 5817 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8550 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨36, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8550 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6604, some c6615, some c6560, some c6814, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p8550 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8550 : lratChecker f8550 p8550 = .success := by decide +kernel
theorem unsat8550 : Unsatisfiable (PosFin 65) f8550 := by
  apply lratCheckerSound f8550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8550
  · intro a ha; simp [p8550] at ha; subst a; trivial
  · exact checked8550
theorem derived8550 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8550 := by
  apply localUnsat_implies_entails f8550 [c6604, c6615, c6560, c6814] c8550 unsat8550 (by rfl) a
  have h0 : Entails.eval a c6604 := h 6603 (by decide)
  have h1 : Entails.eval a c6615 := h 6614 (by decide)
  have h2 : Entails.eval a c6560 := h 6559 (by decide)
  have h3 : Entails.eval a c6814 := h 6813 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8550

end CochromaticTwenty.Certificates.FixedCore0
