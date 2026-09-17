import MerLeanExperiment.Certificates.FixedCore0.Steps0400_0499

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8051 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨64, by decide⟩, false), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8051 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8049, some c8050, some c8010, some c8044, some c1450, some c1393, some c4923, some c2498, some c4197, some c4051, some c2636, some c3355, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p8051 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8051 : lratChecker f8051 p8051 = .success := by decide +kernel
theorem unsat8051 : Unsatisfiable (PosFin 65) f8051 := by
  apply lratCheckerSound f8051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8051
  · intro a ha; simp [p8051] at ha; subst a; trivial
  · exact checked8051
theorem derived8051 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8051 := by
  apply localUnsat_implies_entails f8051 [c8049, c8050, c8010, c8044, c1450, c1393, c4923, c2498, c4197, c4051, c2636, c3355] c8051 unsat8051 (by rfl) a
  have h0 : Entails.eval a c8049 := derived8049 a h
  have h1 : Entails.eval a c8050 := derived8050 a h
  have h2 : Entails.eval a c8010 := derived8010 a h
  have h3 : Entails.eval a c8044 := derived8044 a h
  have h4 : Entails.eval a c1450 := h 1449 (by decide)
  have h5 : Entails.eval a c1393 := h 1392 (by decide)
  have h6 : Entails.eval a c4923 := h 4922 (by decide)
  have h7 : Entails.eval a c2498 := h 2497 (by decide)
  have h8 : Entails.eval a c4197 := h 4196 (by decide)
  have h9 : Entails.eval a c4051 := h 4050 (by decide)
  have h10 : Entails.eval a c2636 := h 2635 (by decide)
  have h11 : Entails.eval a c3355 := h 3354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8052 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8052 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8041, some c8007, some c8048, some c8051, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8052 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8052 : lratChecker f8052 p8052 = .success := by decide +kernel
theorem unsat8052 : Unsatisfiable (PosFin 65) f8052 := by
  apply lratCheckerSound f8052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8052
  · intro a ha; simp [p8052] at ha; subst a; trivial
  · exact checked8052
theorem derived8052 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8052 := by
  apply localUnsat_implies_entails f8052 [c8041, c8007, c8048, c8051] c8052 unsat8052 (by rfl) a
  have h0 : Entails.eval a c8041 := derived8041 a h
  have h1 : Entails.eval a c8007 := derived8007 a h
  have h2 : Entails.eval a c8048 := derived8048 a h
  have h3 : Entails.eval a c8051 := derived8051 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8053 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8053 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4529, some c2654, some c2521, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8053 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8053 : lratChecker f8053 p8053 = .success := by decide +kernel
theorem unsat8053 : Unsatisfiable (PosFin 65) f8053 := by
  apply lratCheckerSound f8053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8053
  · intro a ha; simp [p8053] at ha; subst a; trivial
  · exact checked8053
theorem derived8053 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8053 := by
  apply localUnsat_implies_entails f8053 [c4529, c2654, c2521] c8053 unsat8053 (by rfl) a
  have h0 : Entails.eval a c4529 := h 4528 (by decide)
  have h1 : Entails.eval a c2654 := h 2653 (by decide)
  have h2 : Entails.eval a c2521 := h 2520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8054 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8054 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c5048, some c3684, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8054 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8054 : lratChecker f8054 p8054 = .success := by decide +kernel
theorem unsat8054 : Unsatisfiable (PosFin 65) f8054 := by
  apply lratCheckerSound f8054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8054
  · intro a ha; simp [p8054] at ha; subst a; trivial
  · exact checked8054
theorem derived8054 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8054 := by
  apply localUnsat_implies_entails f8054 [c8007, c5048, c3684] c8054 unsat8054 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c5048 := h 5047 (by decide)
  have h2 : Entails.eval a c3684 := h 3683 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8055 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8055 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8053, some c2963, some c3121, some c3667, some c3355, some c2521, some c2760, some c1114, some c4470, some c4138, some c8054, some c1646, some c1665, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8055 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8055 : lratChecker f8055 p8055 = .success := by decide +kernel
theorem unsat8055 : Unsatisfiable (PosFin 65) f8055 := by
  apply lratCheckerSound f8055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8055
  · intro a ha; simp [p8055] at ha; subst a; trivial
  · exact checked8055
theorem derived8055 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8055 := by
  apply localUnsat_implies_entails f8055 [c8007, c8053, c2963, c3121, c3667, c3355, c2521, c2760, c1114, c4470, c4138, c8054, c1646, c1665] c8055 unsat8055 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8053 := derived8053 a h
  have h2 : Entails.eval a c2963 := h 2962 (by decide)
  have h3 : Entails.eval a c3121 := h 3120 (by decide)
  have h4 : Entails.eval a c3667 := h 3666 (by decide)
  have h5 : Entails.eval a c3355 := h 3354 (by decide)
  have h6 : Entails.eval a c2521 := h 2520 (by decide)
  have h7 : Entails.eval a c2760 := h 2759 (by decide)
  have h8 : Entails.eval a c1114 := h 1113 (by decide)
  have h9 : Entails.eval a c4470 := h 4469 (by decide)
  have h10 : Entails.eval a c4138 := h 4137 (by decide)
  have h11 : Entails.eval a c8054 := derived8054 a h
  have h12 : Entails.eval a c1646 := h 1645 (by decide)
  have h13 : Entails.eval a c1665 := h 1664 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8056 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8056 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8035, some c8041, some c8052, some c8055, some c3412, some c42, some c3441, some c491, some c8044, some c4470, some c6382, some c6808, some c7316, some c69, some c7127, some c5713, some c7069, some c54, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8056 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8056 : lratChecker f8056 p8056 = .success := by decide +kernel
theorem unsat8056 : Unsatisfiable (PosFin 65) f8056 := by
  apply lratCheckerSound f8056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8056
  · intro a ha; simp [p8056] at ha; subst a; trivial
  · exact checked8056
theorem derived8056 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8056 := by
  apply localUnsat_implies_entails f8056 [c8007, c8035, c8041, c8052, c8055, c3412, c42, c3441, c491, c8044, c4470, c6382, c6808, c7316, c69, c7127, c5713, c7069, c54] c8056 unsat8056 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8035 := derived8035 a h
  have h2 : Entails.eval a c8041 := derived8041 a h
  have h3 : Entails.eval a c8052 := derived8052 a h
  have h4 : Entails.eval a c8055 := derived8055 a h
  have h5 : Entails.eval a c3412 := h 3411 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c3441 := h 3440 (by decide)
  have h8 : Entails.eval a c491 := h 490 (by decide)
  have h9 : Entails.eval a c8044 := derived8044 a h
  have h10 : Entails.eval a c4470 := h 4469 (by decide)
  have h11 : Entails.eval a c6382 := h 6381 (by decide)
  have h12 : Entails.eval a c6808 := h 6807 (by decide)
  have h13 : Entails.eval a c7316 := h 7315 (by decide)
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c7127 := h 7126 (by decide)
  have h16 : Entails.eval a c5713 := h 5712 (by decide)
  have h17 : Entails.eval a c7069 := h 7068 (by decide)
  have h18 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8057 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8057 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7493, some c6515, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8057 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8057 : lratChecker f8057 p8057 = .success := by decide +kernel
theorem unsat8057 : Unsatisfiable (PosFin 65) f8057 := by
  apply lratCheckerSound f8057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8057
  · intro a ha; simp [p8057] at ha; subst a; trivial
  · exact checked8057
theorem derived8057 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8057 := by
  apply localUnsat_implies_entails f8057 [c7493, c6515] c8057 unsat8057 (by rfl) a
  have h0 : Entails.eval a c7493 := h 7492 (by decide)
  have h1 : Entails.eval a c6515 := h 6514 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8058 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨58, by decide⟩, false), (⟨55, by decide⟩, false), (⟨44, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8058 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6325, some c6945, some c6481, some c7489, some c6540, some c6382, some c487, some c42, some c473, some c4262, some c91, some c5830, some c5759, some c6036, some c6106, some c6131, some c6061, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8058 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8058 : lratChecker f8058 p8058 = .success := by decide +kernel
theorem unsat8058 : Unsatisfiable (PosFin 65) f8058 := by
  apply lratCheckerSound f8058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8058
  · intro a ha; simp [p8058] at ha; subst a; trivial
  · exact checked8058
theorem derived8058 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8058 := by
  apply localUnsat_implies_entails f8058 [c6325, c6945, c6481, c7489, c6540, c6382, c487, c42, c473, c4262, c91, c5830, c5759, c6036, c6106, c6131, c6061] c8058 unsat8058 (by rfl) a
  have h0 : Entails.eval a c6325 := h 6324 (by decide)
  have h1 : Entails.eval a c6945 := h 6944 (by decide)
  have h2 : Entails.eval a c6481 := h 6480 (by decide)
  have h3 : Entails.eval a c7489 := h 7488 (by decide)
  have h4 : Entails.eval a c6540 := h 6539 (by decide)
  have h5 : Entails.eval a c6382 := h 6381 (by decide)
  have h6 : Entails.eval a c487 := h 486 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c473 := h 472 (by decide)
  have h9 : Entails.eval a c4262 := h 4261 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c5830 := h 5829 (by decide)
  have h12 : Entails.eval a c5759 := h 5758 (by decide)
  have h13 : Entails.eval a c6036 := h 6035 (by decide)
  have h14 : Entails.eval a c6106 := h 6105 (by decide)
  have h15 : Entails.eval a c6131 := h 6130 (by decide)
  have h16 : Entails.eval a c6061 := h 6060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8059 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8059 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8056, some c8007, some c6945, some c6325, some c6481, some c7489, some c8057, some c8058, some c8051, some c8055, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8059 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8059 : lratChecker f8059 p8059 = .success := by decide +kernel
theorem unsat8059 : Unsatisfiable (PosFin 65) f8059 := by
  apply lratCheckerSound f8059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8059
  · intro a ha; simp [p8059] at ha; subst a; trivial
  · exact checked8059
theorem derived8059 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8059 := by
  apply localUnsat_implies_entails f8059 [c8056, c8007, c6945, c6325, c6481, c7489, c8057, c8058, c8051, c8055] c8059 unsat8059 (by rfl) a
  have h0 : Entails.eval a c8056 := derived8056 a h
  have h1 : Entails.eval a c8007 := derived8007 a h
  have h2 : Entails.eval a c6945 := h 6944 (by decide)
  have h3 : Entails.eval a c6325 := h 6324 (by decide)
  have h4 : Entails.eval a c6481 := h 6480 (by decide)
  have h5 : Entails.eval a c7489 := h 7488 (by decide)
  have h6 : Entails.eval a c8057 := derived8057 a h
  have h7 : Entails.eval a c8058 := derived8058 a h
  have h8 : Entails.eval a c8051 := derived8051 a h
  have h9 : Entails.eval a c8055 := derived8055 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8060 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8060 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6316, some c6940, some c8036, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8060 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8060 : lratChecker f8060 p8060 = .success := by decide +kernel
theorem unsat8060 : Unsatisfiable (PosFin 65) f8060 := by
  apply lratCheckerSound f8060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8060
  · intro a ha; simp [p8060] at ha; subst a; trivial
  · exact checked8060
theorem derived8060 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8060 := by
  apply localUnsat_implies_entails f8060 [c6316, c6940, c8036] c8060 unsat8060 (by rfl) a
  have h0 : Entails.eval a c6316 := h 6315 (by decide)
  have h1 : Entails.eval a c6940 := h 6939 (by decide)
  have h2 : Entails.eval a c8036 := derived8036 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8061 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨64, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8061 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8056, some c8059, some c8060, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8061 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8061 : lratChecker f8061 p8061 = .success := by decide +kernel
theorem unsat8061 : Unsatisfiable (PosFin 65) f8061 := by
  apply lratCheckerSound f8061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8061
  · intro a ha; simp [p8061] at ha; subst a; trivial
  · exact checked8061
theorem derived8061 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8061 := by
  apply localUnsat_implies_entails f8061 [c8056, c8059, c8060] c8061 unsat8061 (by rfl) a
  have h0 : Entails.eval a c8056 := derived8056 a h
  have h1 : Entails.eval a c8059 := derived8059 a h
  have h2 : Entails.eval a c8060 := derived8060 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8062 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8062 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6475, some c6547, some c7175, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8062 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8062 : lratChecker f8062 p8062 = .success := by decide +kernel
theorem unsat8062 : Unsatisfiable (PosFin 65) f8062 := by
  apply lratCheckerSound f8062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8062
  · intro a ha; simp [p8062] at ha; subst a; trivial
  · exact checked8062
theorem derived8062 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8062 := by
  apply localUnsat_implies_entails f8062 [c6371, c6475, c6547, c7175] c8062 unsat8062 (by rfl) a
  have h0 : Entails.eval a c6371 := h 6370 (by decide)
  have h1 : Entails.eval a c6475 := h 6474 (by decide)
  have h2 : Entails.eval a c6547 := h 6546 (by decide)
  have h3 : Entails.eval a c7175 := h 7174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8063 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8063 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8062, some c7546, some c6948, some c6512, some c6905, some c7522, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8063 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8063 : lratChecker f8063 p8063 = .success := by decide +kernel
theorem unsat8063 : Unsatisfiable (PosFin 65) f8063 := by
  apply lratCheckerSound f8063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8063
  · intro a ha; simp [p8063] at ha; subst a; trivial
  · exact checked8063
theorem derived8063 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8063 := by
  apply localUnsat_implies_entails f8063 [c8062, c7546, c6948, c6512, c6905, c7522] c8063 unsat8063 (by rfl) a
  have h0 : Entails.eval a c8062 := derived8062 a h
  have h1 : Entails.eval a c7546 := h 7545 (by decide)
  have h2 : Entails.eval a c6948 := h 6947 (by decide)
  have h3 : Entails.eval a c6512 := h 6511 (by decide)
  have h4 : Entails.eval a c6905 := h 6904 (by decide)
  have h5 : Entails.eval a c7522 := h 7521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8064 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8064 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8061, some c8007, some c8063, some c6501, some c6890, some c6920, some c7482, some c7044, some c7507, some c7637, some c6753, some c6619, some c6601, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8064 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8064 : lratChecker f8064 p8064 = .success := by decide +kernel
theorem unsat8064 : Unsatisfiable (PosFin 65) f8064 := by
  apply lratCheckerSound f8064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8064
  · intro a ha; simp [p8064] at ha; subst a; trivial
  · exact checked8064
theorem derived8064 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8064 := by
  apply localUnsat_implies_entails f8064 [c8061, c8007, c8063, c6501, c6890, c6920, c7482, c7044, c7507, c7637, c6753, c6619, c6601] c8064 unsat8064 (by rfl) a
  have h0 : Entails.eval a c8061 := derived8061 a h
  have h1 : Entails.eval a c8007 := derived8007 a h
  have h2 : Entails.eval a c8063 := derived8063 a h
  have h3 : Entails.eval a c6501 := h 6500 (by decide)
  have h4 : Entails.eval a c6890 := h 6889 (by decide)
  have h5 : Entails.eval a c6920 := h 6919 (by decide)
  have h6 : Entails.eval a c7482 := h 7481 (by decide)
  have h7 : Entails.eval a c7044 := h 7043 (by decide)
  have h8 : Entails.eval a c7507 := h 7506 (by decide)
  have h9 : Entails.eval a c7637 := derived7637 a h
  have h10 : Entails.eval a c6753 := h 6752 (by decide)
  have h11 : Entails.eval a c6619 := h 6618 (by decide)
  have h12 : Entails.eval a c6601 := h 6600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8065 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8065 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8061, some c8007, some c6905, some c6486, some c7812, some c6602, some c6587, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8065 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8065 : lratChecker f8065 p8065 = .success := by decide +kernel
theorem unsat8065 : Unsatisfiable (PosFin 65) f8065 := by
  apply lratCheckerSound f8065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8065
  · intro a ha; simp [p8065] at ha; subst a; trivial
  · exact checked8065
theorem derived8065 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8065 := by
  apply localUnsat_implies_entails f8065 [c8061, c8007, c6905, c6486, c7812, c6602, c6587] c8065 unsat8065 (by rfl) a
  have h0 : Entails.eval a c8061 := derived8061 a h
  have h1 : Entails.eval a c8007 := derived8007 a h
  have h2 : Entails.eval a c6905 := h 6904 (by decide)
  have h3 : Entails.eval a c6486 := h 6485 (by decide)
  have h4 : Entails.eval a c7812 := derived7812 a h
  have h5 : Entails.eval a c6602 := h 6601 (by decide)
  have h6 : Entails.eval a c6587 := h 6586 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8066 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8066 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7026, some c7161, some c6959, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8066 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8066 : lratChecker f8066 p8066 = .success := by decide +kernel
theorem unsat8066 : Unsatisfiable (PosFin 65) f8066 := by
  apply lratCheckerSound f8066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8066
  · intro a ha; simp [p8066] at ha; subst a; trivial
  · exact checked8066
theorem derived8066 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8066 := by
  apply localUnsat_implies_entails f8066 [c7026, c7161, c6959] c8066 unsat8066 (by rfl) a
  have h0 : Entails.eval a c7026 := h 7025 (by decide)
  have h1 : Entails.eval a c7161 := h 7160 (by decide)
  have h2 : Entails.eval a c6959 := h 6958 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8067 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8067 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8064, some c8061, some c8065, some c8066, some c6874, some c6890, some c6486, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8067 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8067 : lratChecker f8067 p8067 = .success := by decide +kernel
theorem unsat8067 : Unsatisfiable (PosFin 65) f8067 := by
  apply lratCheckerSound f8067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8067
  · intro a ha; simp [p8067] at ha; subst a; trivial
  · exact checked8067
theorem derived8067 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8067 := by
  apply localUnsat_implies_entails f8067 [c8064, c8061, c8065, c8066, c6874, c6890, c6486] c8067 unsat8067 (by rfl) a
  have h0 : Entails.eval a c8064 := derived8064 a h
  have h1 : Entails.eval a c8061 := derived8061 a h
  have h2 : Entails.eval a c8065 := derived8065 a h
  have h3 : Entails.eval a c8066 := derived8066 a h
  have h4 : Entails.eval a c6874 := h 6873 (by decide)
  have h5 : Entails.eval a c6890 := h 6889 (by decide)
  have h6 : Entails.eval a c6486 := h 6485 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8068 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨33, by decide⟩, true), (⟨44, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8068 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8062, some c8066, some c7358, some c6404, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8068 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8068 : lratChecker f8068 p8068 = .success := by decide +kernel
theorem unsat8068 : Unsatisfiable (PosFin 65) f8068 := by
  apply lratCheckerSound f8068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8068
  · intro a ha; simp [p8068] at ha; subst a; trivial
  · exact checked8068
theorem derived8068 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8068 := by
  apply localUnsat_implies_entails f8068 [c8062, c8066, c7358, c6404] c8068 unsat8068 (by rfl) a
  have h0 : Entails.eval a c8062 := derived8062 a h
  have h1 : Entails.eval a c8066 := derived8066 a h
  have h2 : Entails.eval a c7358 := h 7357 (by decide)
  have h3 : Entails.eval a c6404 := h 6403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8069 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8069 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8061, some c8064, some c8067, some c8068, some c6948, some c6512, some c6905, some c7522, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8069 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8069 : lratChecker f8069 p8069 = .success := by decide +kernel
theorem unsat8069 : Unsatisfiable (PosFin 65) f8069 := by
  apply lratCheckerSound f8069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8069
  · intro a ha; simp [p8069] at ha; subst a; trivial
  · exact checked8069
theorem derived8069 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8069 := by
  apply localUnsat_implies_entails f8069 [c8061, c8064, c8067, c8068, c6948, c6512, c6905, c7522] c8069 unsat8069 (by rfl) a
  have h0 : Entails.eval a c8061 := derived8061 a h
  have h1 : Entails.eval a c8064 := derived8064 a h
  have h2 : Entails.eval a c8067 := derived8067 a h
  have h3 : Entails.eval a c8068 := derived8068 a h
  have h4 : Entails.eval a c6948 := h 6947 (by decide)
  have h5 : Entails.eval a c6512 := h 6511 (by decide)
  have h6 : Entails.eval a c6905 := h 6904 (by decide)
  have h7 : Entails.eval a c7522 := h 7521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8070 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8070 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8069, some c8061, some c8007, some c6600, some c6914, some c6649, some c6775, some c7553, some c6462, some c6949, some c7009, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8070 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8070 : lratChecker f8070 p8070 = .success := by decide +kernel
theorem unsat8070 : Unsatisfiable (PosFin 65) f8070 := by
  apply lratCheckerSound f8070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8070
  · intro a ha; simp [p8070] at ha; subst a; trivial
  · exact checked8070
theorem derived8070 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8070 := by
  apply localUnsat_implies_entails f8070 [c8069, c8061, c8007, c6600, c6914, c6649, c6775, c7553, c6462, c6949, c7009] c8070 unsat8070 (by rfl) a
  have h0 : Entails.eval a c8069 := derived8069 a h
  have h1 : Entails.eval a c8061 := derived8061 a h
  have h2 : Entails.eval a c8007 := derived8007 a h
  have h3 : Entails.eval a c6600 := h 6599 (by decide)
  have h4 : Entails.eval a c6914 := h 6913 (by decide)
  have h5 : Entails.eval a c6649 := h 6648 (by decide)
  have h6 : Entails.eval a c6775 := h 6774 (by decide)
  have h7 : Entails.eval a c7553 := derived7553 a h
  have h8 : Entails.eval a c6462 := h 6461 (by decide)
  have h9 : Entails.eval a c6949 := h 6948 (by decide)
  have h10 : Entails.eval a c7009 := h 7008 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8071 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨35, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8071 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6775, some c6838, some c7034, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8071 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8071 : lratChecker f8071 p8071 = .success := by decide +kernel
theorem unsat8071 : Unsatisfiable (PosFin 65) f8071 := by
  apply lratCheckerSound f8071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8071
  · intro a ha; simp [p8071] at ha; subst a; trivial
  · exact checked8071
theorem derived8071 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8071 := by
  apply localUnsat_implies_entails f8071 [c6775, c6838, c7034] c8071 unsat8071 (by rfl) a
  have h0 : Entails.eval a c6775 := h 6774 (by decide)
  have h1 : Entails.eval a c6838 := h 6837 (by decide)
  have h2 : Entails.eval a c7034 := h 7033 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8072 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8072 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8069, some c8061, some c8007, some c8070, some c8071, some c7364, some c6382, some c7142, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8072 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8072 : lratChecker f8072 p8072 = .success := by decide +kernel
theorem unsat8072 : Unsatisfiable (PosFin 65) f8072 := by
  apply lratCheckerSound f8072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8072
  · intro a ha; simp [p8072] at ha; subst a; trivial
  · exact checked8072
theorem derived8072 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8072 := by
  apply localUnsat_implies_entails f8072 [c8069, c8061, c8007, c8070, c8071, c7364, c6382, c7142] c8072 unsat8072 (by rfl) a
  have h0 : Entails.eval a c8069 := derived8069 a h
  have h1 : Entails.eval a c8061 := derived8061 a h
  have h2 : Entails.eval a c8007 := derived8007 a h
  have h3 : Entails.eval a c8070 := derived8070 a h
  have h4 : Entails.eval a c8071 := derived8071 a h
  have h5 : Entails.eval a c7364 := h 7363 (by decide)
  have h6 : Entails.eval a c6382 := h 6381 (by decide)
  have h7 : Entails.eval a c7142 := h 7141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8073 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8073 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7364, some c7142, some c7305, some c7223, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p8073 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8073 : lratChecker f8073 p8073 = .success := by decide +kernel
theorem unsat8073 : Unsatisfiable (PosFin 65) f8073 := by
  apply lratCheckerSound f8073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8073
  · intro a ha; simp [p8073] at ha; subst a; trivial
  · exact checked8073
theorem derived8073 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8073 := by
  apply localUnsat_implies_entails f8073 [c7364, c7142, c7305, c7223] c8073 unsat8073 (by rfl) a
  have h0 : Entails.eval a c7364 := h 7363 (by decide)
  have h1 : Entails.eval a c7142 := h 7141 (by decide)
  have h2 : Entails.eval a c7305 := h 7304 (by decide)
  have h3 : Entails.eval a c7223 := h 7222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8074 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false), (⟨35, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8074 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8071, some c8073, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p8074 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8074 : lratChecker f8074 p8074 = .success := by decide +kernel
theorem unsat8074 : Unsatisfiable (PosFin 65) f8074 := by
  apply lratCheckerSound f8074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8074
  · intro a ha; simp [p8074] at ha; subst a; trivial
  · exact checked8074
theorem derived8074 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8074 := by
  apply localUnsat_implies_entails f8074 [c8071, c8073] c8074 unsat8074 (by rfl) a
  have h0 : Entails.eval a c8071 := derived8071 a h
  have h1 : Entails.eval a c8073 := derived8073 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8075 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8075 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c8061, some c8069, some c8072, some c8074, some c6600, some c6914, some c6282, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8075 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8075 : lratChecker f8075 p8075 = .success := by decide +kernel
theorem unsat8075 : Unsatisfiable (PosFin 65) f8075 := by
  apply lratCheckerSound f8075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8075
  · intro a ha; simp [p8075] at ha; subst a; trivial
  · exact checked8075
theorem derived8075 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8075 := by
  apply localUnsat_implies_entails f8075 [c8007, c8061, c8069, c8072, c8074, c6600, c6914, c6282] c8075 unsat8075 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c8061 := derived8061 a h
  have h2 : Entails.eval a c8069 := derived8069 a h
  have h3 : Entails.eval a c8072 := derived8072 a h
  have h4 : Entails.eval a c8074 := derived8074 a h
  have h5 : Entails.eval a c6600 := h 6599 (by decide)
  have h6 : Entails.eval a c6914 := h 6913 (by decide)
  have h7 : Entails.eval a c6282 := h 6281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8076 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨58, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨62, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8076 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6706, some c7040, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8076 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8076 : lratChecker f8076 p8076 = .success := by decide +kernel
theorem unsat8076 : Unsatisfiable (PosFin 65) f8076 := by
  apply lratCheckerSound f8076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8076
  · intro a ha; simp [p8076] at ha; subst a; trivial
  · exact checked8076
theorem derived8076 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8076 := by
  apply localUnsat_implies_entails f8076 [c6706, c7040] c8076 unsat8076 (by rfl) a
  have h0 : Entails.eval a c6706 := h 6705 (by decide)
  have h1 : Entails.eval a c7040 := h 7039 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8077 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8077 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6914, some c6600, some c6282, some c6649, some c6775, some c6838, some c7553, some c6685, some c7316, some c7194, some c8076, some c6399, some c6847, some c6441, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8077 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8077 : lratChecker f8077 p8077 = .success := by decide +kernel
theorem unsat8077 : Unsatisfiable (PosFin 65) f8077 := by
  apply lratCheckerSound f8077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8077
  · intro a ha; simp [p8077] at ha; subst a; trivial
  · exact checked8077
theorem derived8077 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8077 := by
  apply localUnsat_implies_entails f8077 [c7994, c6914, c6600, c6282, c6649, c6775, c6838, c7553, c6685, c7316, c7194, c8076, c6399, c6847, c6441] c8077 unsat8077 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6914 := h 6913 (by decide)
  have h2 : Entails.eval a c6600 := h 6599 (by decide)
  have h3 : Entails.eval a c6282 := h 6281 (by decide)
  have h4 : Entails.eval a c6649 := h 6648 (by decide)
  have h5 : Entails.eval a c6775 := h 6774 (by decide)
  have h6 : Entails.eval a c6838 := h 6837 (by decide)
  have h7 : Entails.eval a c7553 := derived7553 a h
  have h8 : Entails.eval a c6685 := h 6684 (by decide)
  have h9 : Entails.eval a c7316 := h 7315 (by decide)
  have h10 : Entails.eval a c7194 := h 7193 (by decide)
  have h11 : Entails.eval a c8076 := derived8076 a h
  have h12 : Entails.eval a c6399 := h 6398 (by decide)
  have h13 : Entails.eval a c6847 := h 6846 (by decide)
  have h14 : Entails.eval a c6441 := h 6440 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8078 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8078 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6282, some c6649, some c6414, some c6685, some c7316, some c7194, some c6936, some c6382, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8078 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8078 : lratChecker f8078 p8078 = .success := by decide +kernel
theorem unsat8078 : Unsatisfiable (PosFin 65) f8078 := by
  apply lratCheckerSound f8078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8078
  · intro a ha; simp [p8078] at ha; subst a; trivial
  · exact checked8078
theorem derived8078 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8078 := by
  apply localUnsat_implies_entails f8078 [c6282, c6649, c6414, c6685, c7316, c7194, c6936, c6382] c8078 unsat8078 (by rfl) a
  have h0 : Entails.eval a c6282 := h 6281 (by decide)
  have h1 : Entails.eval a c6649 := h 6648 (by decide)
  have h2 : Entails.eval a c6414 := h 6413 (by decide)
  have h3 : Entails.eval a c6685 := h 6684 (by decide)
  have h4 : Entails.eval a c7316 := h 7315 (by decide)
  have h5 : Entails.eval a c7194 := h 7193 (by decide)
  have h6 : Entails.eval a c6936 := h 6935 (by decide)
  have h7 : Entails.eval a c6382 := h 6381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8079 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8079 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6945, some c6936, some c7316, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8079 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8079 : lratChecker f8079 p8079 = .success := by decide +kernel
theorem unsat8079 : Unsatisfiable (PosFin 65) f8079 := by
  apply lratCheckerSound f8079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8079
  · intro a ha; simp [p8079] at ha; subst a; trivial
  · exact checked8079
theorem derived8079 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8079 := by
  apply localUnsat_implies_entails f8079 [c6945, c6936, c7316] c8079 unsat8079 (by rfl) a
  have h0 : Entails.eval a c6945 := h 6944 (by decide)
  have h1 : Entails.eval a c6936 := h 6935 (by decide)
  have h2 : Entails.eval a c7316 := h 7315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8080 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8080 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6443, some c6438, some c6432, some c6442, some c6529, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8080 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8080 : lratChecker f8080 p8080 = .success := by decide +kernel
theorem unsat8080 : Unsatisfiable (PosFin 65) f8080 := by
  apply lratCheckerSound f8080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8080
  · intro a ha; simp [p8080] at ha; subst a; trivial
  · exact checked8080
theorem derived8080 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8080 := by
  apply localUnsat_implies_entails f8080 [c6443, c6438, c6432, c6442, c6529] c8080 unsat8080 (by rfl) a
  have h0 : Entails.eval a c6443 := h 6442 (by decide)
  have h1 : Entails.eval a c6438 := h 6437 (by decide)
  have h2 : Entails.eval a c6432 := h 6431 (by decide)
  have h3 : Entails.eval a c6442 := h 6441 (by decide)
  have h4 : Entails.eval a c6529 := h 6528 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8081 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨62, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8081 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7050, some c7056, some c7040, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8081 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8081 : lratChecker f8081 p8081 = .success := by decide +kernel
theorem unsat8081 : Unsatisfiable (PosFin 65) f8081 := by
  apply lratCheckerSound f8081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8081
  · intro a ha; simp [p8081] at ha; subst a; trivial
  · exact checked8081
theorem derived8081 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8081 := by
  apply localUnsat_implies_entails f8081 [c7050, c7056, c7040] c8081 unsat8081 (by rfl) a
  have h0 : Entails.eval a c7050 := h 7049 (by decide)
  have h1 : Entails.eval a c7056 := h 7055 (by decide)
  have h2 : Entails.eval a c7040 := h 7039 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8082 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8082 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c7182, some c6823, some c7497, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8082 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8082 : lratChecker f8082 p8082 = .success := by decide +kernel
theorem unsat8082 : Unsatisfiable (PosFin 65) f8082 := by
  apply lratCheckerSound f8082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8082
  · intro a ha; simp [p8082] at ha; subst a; trivial
  · exact checked8082
theorem derived8082 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8082 := by
  apply localUnsat_implies_entails f8082 [c7994, c7182, c6823, c7497] c8082 unsat8082 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c7182 := h 7181 (by decide)
  have h2 : Entails.eval a c6823 := h 6822 (by decide)
  have h3 : Entails.eval a c7497 := h 7496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8083 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8083 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8079, some c7994, some c6382, some c6808, some c7316, some c8082, some c7328, some c6527, some c6749, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8083 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8083 : lratChecker f8083 p8083 = .success := by decide +kernel
theorem unsat8083 : Unsatisfiable (PosFin 65) f8083 := by
  apply lratCheckerSound f8083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8083
  · intro a ha; simp [p8083] at ha; subst a; trivial
  · exact checked8083
theorem derived8083 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8083 := by
  apply localUnsat_implies_entails f8083 [c8079, c7994, c6382, c6808, c7316, c8082, c7328, c6527, c6749] c8083 unsat8083 (by rfl) a
  have h0 : Entails.eval a c8079 := derived8079 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c6382 := h 6381 (by decide)
  have h3 : Entails.eval a c6808 := h 6807 (by decide)
  have h4 : Entails.eval a c7316 := h 7315 (by decide)
  have h5 : Entails.eval a c8082 := derived8082 a h
  have h6 : Entails.eval a c7328 := h 7327 (by decide)
  have h7 : Entails.eval a c6527 := h 6526 (by decide)
  have h8 : Entails.eval a c6749 := h 6748 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8084 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8084 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6325, some c6310, some c7316, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8084 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8084 : lratChecker f8084 p8084 = .success := by decide +kernel
theorem unsat8084 : Unsatisfiable (PosFin 65) f8084 := by
  apply lratCheckerSound f8084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8084
  · intro a ha; simp [p8084] at ha; subst a; trivial
  · exact checked8084
theorem derived8084 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8084 := by
  apply localUnsat_implies_entails f8084 [c6325, c6310, c7316] c8084 unsat8084 (by rfl) a
  have h0 : Entails.eval a c6325 := h 6324 (by decide)
  have h1 : Entails.eval a c6310 := h 6309 (by decide)
  have h2 : Entails.eval a c7316 := h 7315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8085 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8085 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8079, some c8084, some c6481, some c8083, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8085 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8085 : lratChecker f8085 p8085 = .success := by decide +kernel
theorem unsat8085 : Unsatisfiable (PosFin 65) f8085 := by
  apply lratCheckerSound f8085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8085
  · intro a ha; simp [p8085] at ha; subst a; trivial
  · exact checked8085
theorem derived8085 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8085 := by
  apply localUnsat_implies_entails f8085 [c8079, c8084, c6481, c8083] c8085 unsat8085 (by rfl) a
  have h0 : Entails.eval a c8079 := derived8079 a h
  have h1 : Entails.eval a c8084 := derived8084 a h
  have h2 : Entails.eval a c6481 := h 6480 (by decide)
  have h3 : Entails.eval a c8083 := derived8083 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8086 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8086 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8078, some c8085, some c7127, some c7297, some c6636, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8086 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8086 : lratChecker f8086 p8086 = .success := by decide +kernel
theorem unsat8086 : Unsatisfiable (PosFin 65) f8086 := by
  apply lratCheckerSound f8086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8086
  · intro a ha; simp [p8086] at ha; subst a; trivial
  · exact checked8086
theorem derived8086 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8086 := by
  apply localUnsat_implies_entails f8086 [c8078, c8085, c7127, c7297, c6636] c8086 unsat8086 (by rfl) a
  have h0 : Entails.eval a c8078 := derived8078 a h
  have h1 : Entails.eval a c8085 := derived8085 a h
  have h2 : Entails.eval a c7127 := h 7126 (by decide)
  have h3 : Entails.eval a c7297 := h 7296 (by decide)
  have h4 : Entails.eval a c6636 := h 6635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8087 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8087 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c7281, some c6869, some c7269, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8087 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8087 : lratChecker f8087 p8087 = .success := by decide +kernel
theorem unsat8087 : Unsatisfiable (PosFin 65) f8087 := by
  apply lratCheckerSound f8087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8087
  · intro a ha; simp [p8087] at ha; subst a; trivial
  · exact checked8087
theorem derived8087 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8087 := by
  apply localUnsat_implies_entails f8087 [c7994, c7281, c6869, c7269] c8087 unsat8087 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c7281 := h 7280 (by decide)
  have h2 : Entails.eval a c6869 := h 6868 (by decide)
  have h3 : Entails.eval a c7269 := h 7268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8088 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8088 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6636, some c6610, some c6338, some c6382, some c6945, some c8087, some c6676, some c7155, some c6466, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8088 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8088 : lratChecker f8088 p8088 = .success := by decide +kernel
theorem unsat8088 : Unsatisfiable (PosFin 65) f8088 := by
  apply lratCheckerSound f8088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8088
  · intro a ha; simp [p8088] at ha; subst a; trivial
  · exact checked8088
theorem derived8088 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8088 := by
  apply localUnsat_implies_entails f8088 [c7994, c6636, c6610, c6338, c6382, c6945, c8087, c6676, c7155, c6466] c8088 unsat8088 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6636 := h 6635 (by decide)
  have h2 : Entails.eval a c6610 := h 6609 (by decide)
  have h3 : Entails.eval a c6338 := h 6337 (by decide)
  have h4 : Entails.eval a c6382 := h 6381 (by decide)
  have h5 : Entails.eval a c6945 := h 6944 (by decide)
  have h6 : Entails.eval a c8087 := derived8087 a h
  have h7 : Entails.eval a c6676 := h 6675 (by decide)
  have h8 : Entails.eval a c7155 := h 7154 (by decide)
  have h9 : Entails.eval a c6466 := h 6465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8089 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8089 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8088, some c6808, some c6724, some c7994, some c6945, some c8087, some c6676, some c6470, some c7418, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8089 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8089 : lratChecker f8089 p8089 = .success := by decide +kernel
theorem unsat8089 : Unsatisfiable (PosFin 65) f8089 := by
  apply lratCheckerSound f8089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8089
  · intro a ha; simp [p8089] at ha; subst a; trivial
  · exact checked8089
theorem derived8089 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8089 := by
  apply localUnsat_implies_entails f8089 [c8088, c6808, c6724, c7994, c6945, c8087, c6676, c6470, c7418] c8089 unsat8089 (by rfl) a
  have h0 : Entails.eval a c8088 := derived8088 a h
  have h1 : Entails.eval a c6808 := h 6807 (by decide)
  have h2 : Entails.eval a c6724 := h 6723 (by decide)
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c6945 := h 6944 (by decide)
  have h5 : Entails.eval a c8087 := derived8087 a h
  have h6 : Entails.eval a c6676 := h 6675 (by decide)
  have h7 : Entails.eval a c6470 := h 6469 (by decide)
  have h8 : Entails.eval a c7418 := h 7417 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8090 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8090 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8077, some c8088, some c8086, some c8089, some c6481, some c7081, some c8081, some c6533, some c6540, some c6545, some c7173, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8090 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8090 : lratChecker f8090 p8090 = .success := by decide +kernel
theorem unsat8090 : Unsatisfiable (PosFin 65) f8090 := by
  apply lratCheckerSound f8090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8090
  · intro a ha; simp [p8090] at ha; subst a; trivial
  · exact checked8090
theorem derived8090 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8090 := by
  apply localUnsat_implies_entails f8090 [c8075, c8077, c8088, c8086, c8089, c6481, c7081, c8081, c6533, c6540, c6545, c7173] c8090 unsat8090 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8077 := derived8077 a h
  have h2 : Entails.eval a c8088 := derived8088 a h
  have h3 : Entails.eval a c8086 := derived8086 a h
  have h4 : Entails.eval a c8089 := derived8089 a h
  have h5 : Entails.eval a c6481 := h 6480 (by decide)
  have h6 : Entails.eval a c7081 := h 7080 (by decide)
  have h7 : Entails.eval a c8081 := derived8081 a h
  have h8 : Entails.eval a c6533 := h 6532 (by decide)
  have h9 : Entails.eval a c6540 := h 6539 (by decide)
  have h10 : Entails.eval a c6545 := h 6544 (by decide)
  have h11 : Entails.eval a c7173 := h 7172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8091 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8091 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8077, some c8086, some c8088, some c6808, some c6724, some c8090, some c6325, some c6338, some c7069, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8091 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8091 : lratChecker f8091 p8091 = .success := by decide +kernel
theorem unsat8091 : Unsatisfiable (PosFin 65) f8091 := by
  apply lratCheckerSound f8091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8091
  · intro a ha; simp [p8091] at ha; subst a; trivial
  · exact checked8091
theorem derived8091 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8091 := by
  apply localUnsat_implies_entails f8091 [c8075, c8077, c8086, c8088, c6808, c6724, c8090, c6325, c6338, c7069] c8091 unsat8091 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8077 := derived8077 a h
  have h2 : Entails.eval a c8086 := derived8086 a h
  have h3 : Entails.eval a c8088 := derived8088 a h
  have h4 : Entails.eval a c6808 := h 6807 (by decide)
  have h5 : Entails.eval a c6724 := h 6723 (by decide)
  have h6 : Entails.eval a c8090 := derived8090 a h
  have h7 : Entails.eval a c6325 := h 6324 (by decide)
  have h8 : Entails.eval a c6338 := h 6337 (by decide)
  have h9 : Entails.eval a c7069 := h 7068 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8092 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8092 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8032, some c8026, some c425, some c42, some c8020, some c7649, some c8044, some c54, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8092 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8092 : lratChecker f8092 p8092 = .success := by decide +kernel
theorem unsat8092 : Unsatisfiable (PosFin 65) f8092 := by
  apply lratCheckerSound f8092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8092
  · intro a ha; simp [p8092] at ha; subst a; trivial
  · exact checked8092
theorem derived8092 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8092 := by
  apply localUnsat_implies_entails f8092 [c8032, c8026, c425, c42, c8020, c7649, c8044, c54] c8092 unsat8092 (by rfl) a
  have h0 : Entails.eval a c8032 := derived8032 a h
  have h1 : Entails.eval a c8026 := derived8026 a h
  have h2 : Entails.eval a c425 := h 424 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c8020 := derived8020 a h
  have h5 : Entails.eval a c7649 := derived7649 a h
  have h6 : Entails.eval a c8044 := derived8044 a h
  have h7 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8093 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8093 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8077, some c8086, some c8091, some c6664, some c7081, some c7453, some c6685, some c8081, some c8092, some c6382, some c6533, some c6540, some c6545, some c7173, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8093 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8093 : lratChecker f8093 p8093 = .success := by decide +kernel
theorem unsat8093 : Unsatisfiable (PosFin 65) f8093 := by
  apply lratCheckerSound f8093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8093
  · intro a ha; simp [p8093] at ha; subst a; trivial
  · exact checked8093
theorem derived8093 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8093 := by
  apply localUnsat_implies_entails f8093 [c8075, c8077, c8086, c8091, c6664, c7081, c7453, c6685, c8081, c8092, c6382, c6533, c6540, c6545, c7173] c8093 unsat8093 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8077 := derived8077 a h
  have h2 : Entails.eval a c8086 := derived8086 a h
  have h3 : Entails.eval a c8091 := derived8091 a h
  have h4 : Entails.eval a c6664 := h 6663 (by decide)
  have h5 : Entails.eval a c7081 := h 7080 (by decide)
  have h6 : Entails.eval a c7453 := h 7452 (by decide)
  have h7 : Entails.eval a c6685 := h 6684 (by decide)
  have h8 : Entails.eval a c8081 := derived8081 a h
  have h9 : Entails.eval a c8092 := derived8092 a h
  have h10 : Entails.eval a c6382 := h 6381 (by decide)
  have h11 : Entails.eval a c6533 := h 6532 (by decide)
  have h12 : Entails.eval a c6540 := h 6539 (by decide)
  have h13 : Entails.eval a c6545 := h 6544 (by decide)
  have h14 : Entails.eval a c7173 := h 7172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8094 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8094 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8077, some c8086, some c8093, some c8079, some c8084, some c7081, some c7453, some c8080, some c8081, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8094 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8094 : lratChecker f8094 p8094 = .success := by decide +kernel
theorem unsat8094 : Unsatisfiable (PosFin 65) f8094 := by
  apply lratCheckerSound f8094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8094
  · intro a ha; simp [p8094] at ha; subst a; trivial
  · exact checked8094
theorem derived8094 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8094 := by
  apply localUnsat_implies_entails f8094 [c8075, c8077, c8086, c8093, c8079, c8084, c7081, c7453, c8080, c8081] c8094 unsat8094 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8077 := derived8077 a h
  have h2 : Entails.eval a c8086 := derived8086 a h
  have h3 : Entails.eval a c8093 := derived8093 a h
  have h4 : Entails.eval a c8079 := derived8079 a h
  have h5 : Entails.eval a c8084 := derived8084 a h
  have h6 : Entails.eval a c7081 := h 7080 (by decide)
  have h7 : Entails.eval a c7453 := h 7452 (by decide)
  have h8 : Entails.eval a c8080 := derived8080 a h
  have h9 : Entails.eval a c8081 := derived8081 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8095 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8095 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6437, some c6439, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8095 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8095 : lratChecker f8095 p8095 = .success := by decide +kernel
theorem unsat8095 : Unsatisfiable (PosFin 65) f8095 := by
  apply lratCheckerSound f8095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8095
  · intro a ha; simp [p8095] at ha; subst a; trivial
  · exact checked8095
theorem derived8095 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8095 := by
  apply localUnsat_implies_entails f8095 [c6440, c6437, c6439] c8095 unsat8095 (by rfl) a
  have h0 : Entails.eval a c6440 := h 6439 (by decide)
  have h1 : Entails.eval a c6437 := h 6436 (by decide)
  have h2 : Entails.eval a c6439 := h 6438 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8096 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8096 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6403, some c6408, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8096 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8096 : lratChecker f8096 p8096 = .success := by decide +kernel
theorem unsat8096 : Unsatisfiable (PosFin 65) f8096 := by
  apply lratCheckerSound f8096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8096
  · intro a ha; simp [p8096] at ha; subst a; trivial
  · exact checked8096
theorem derived8096 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8096 := by
  apply localUnsat_implies_entails f8096 [c6403, c6408] c8096 unsat8096 (by rfl) a
  have h0 : Entails.eval a c6403 := h 6402 (by decide)
  have h1 : Entails.eval a c6408 := h 6407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8097 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8097 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6518, some c6852, some c6467, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8097 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8097 : lratChecker f8097 p8097 = .success := by decide +kernel
theorem unsat8097 : Unsatisfiable (PosFin 65) f8097 := by
  apply lratCheckerSound f8097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8097
  · intro a ha; simp [p8097] at ha; subst a; trivial
  · exact checked8097
theorem derived8097 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8097 := by
  apply localUnsat_implies_entails f8097 [c6518, c6852, c6467] c8097 unsat8097 (by rfl) a
  have h0 : Entails.eval a c6518 := h 6517 (by decide)
  have h1 : Entails.eval a c6852 := h 6851 (by decide)
  have h2 : Entails.eval a c6467 := h 6466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8098 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8098 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8097, some c8094, some c7994, some c8095, some c8096, some c6698, some c6677, some c7436, some c6370, some c6805, some c7306, some c8082, some c6544, some c6747, some c6748, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8098 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8098 : lratChecker f8098 p8098 = .success := by decide +kernel
theorem unsat8098 : Unsatisfiable (PosFin 65) f8098 := by
  apply lratCheckerSound f8098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8098
  · intro a ha; simp [p8098] at ha; subst a; trivial
  · exact checked8098
theorem derived8098 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8098 := by
  apply localUnsat_implies_entails f8098 [c8075, c8097, c8094, c7994, c8095, c8096, c6698, c6677, c7436, c6370, c6805, c7306, c8082, c6544, c6747, c6748] c8098 unsat8098 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8097 := derived8097 a h
  have h2 : Entails.eval a c8094 := derived8094 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8095 := derived8095 a h
  have h5 : Entails.eval a c8096 := derived8096 a h
  have h6 : Entails.eval a c6698 := h 6697 (by decide)
  have h7 : Entails.eval a c6677 := h 6676 (by decide)
  have h8 : Entails.eval a c7436 := h 7435 (by decide)
  have h9 : Entails.eval a c6370 := h 6369 (by decide)
  have h10 : Entails.eval a c6805 := h 6804 (by decide)
  have h11 : Entails.eval a c7306 := h 7305 (by decide)
  have h12 : Entails.eval a c8082 := derived8082 a h
  have h13 : Entails.eval a c6544 := h 6543 (by decide)
  have h14 : Entails.eval a c6747 := h 6746 (by decide)
  have h15 : Entails.eval a c6748 := h 6747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8099 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8099 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8094, some c8075, some c7994, some c8097, some c8098, some c6535, some c6468, some c7262, some c7274, some c7213, some c6473, some c6805, some c6698, some c6719, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8099 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8099 : lratChecker f8099 p8099 = .success := by decide +kernel
theorem unsat8099 : Unsatisfiable (PosFin 65) f8099 := by
  apply lratCheckerSound f8099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8099
  · intro a ha; simp [p8099] at ha; subst a; trivial
  · exact checked8099
theorem derived8099 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8099 := by
  apply localUnsat_implies_entails f8099 [c8094, c8075, c7994, c8097, c8098, c6535, c6468, c7262, c7274, c7213, c6473, c6805, c6698, c6719] c8099 unsat8099 (by rfl) a
  have h0 : Entails.eval a c8094 := derived8094 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8097 := derived8097 a h
  have h4 : Entails.eval a c8098 := derived8098 a h
  have h5 : Entails.eval a c6535 := h 6534 (by decide)
  have h6 : Entails.eval a c6468 := h 6467 (by decide)
  have h7 : Entails.eval a c7262 := h 7261 (by decide)
  have h8 : Entails.eval a c7274 := h 7273 (by decide)
  have h9 : Entails.eval a c7213 := h 7212 (by decide)
  have h10 : Entails.eval a c6473 := h 6472 (by decide)
  have h11 : Entails.eval a c6805 := h 6804 (by decide)
  have h12 : Entails.eval a c6698 := h 6697 (by decide)
  have h13 : Entails.eval a c6719 := h 6718 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8100 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8100 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c7061, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8100 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8100 : lratChecker f8100 p8100 = .success := by decide +kernel
theorem unsat8100 : Unsatisfiable (PosFin 65) f8100 := by
  apply lratCheckerSound f8100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8100
  · intro a ha; simp [p8100] at ha; subst a; trivial
  · exact checked8100
theorem derived8100 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8100 := by
  apply localUnsat_implies_entails f8100 [c7060, c7061] c8100 unsat8100 (by rfl) a
  have h0 : Entails.eval a c7060 := h 7059 (by decide)
  have h1 : Entails.eval a c7061 := h 7060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8101 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8101 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c423, some c478, some c469, some c1521, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8101 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8101 : lratChecker f8101 p8101 = .success := by decide +kernel
theorem unsat8101 : Unsatisfiable (PosFin 65) f8101 := by
  apply lratCheckerSound f8101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8101
  · intro a ha; simp [p8101] at ha; subst a; trivial
  · exact checked8101
theorem derived8101 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8101 := by
  apply localUnsat_implies_entails f8101 [c423, c478, c469, c1521] c8101 unsat8101 (by rfl) a
  have h0 : Entails.eval a c423 := h 422 (by decide)
  have h1 : Entails.eval a c478 := h 477 (by decide)
  have h2 : Entails.eval a c469 := h 468 (by decide)
  have h3 : Entails.eval a c1521 := h 1520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8102 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8102 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1498, some c1556, some c1655, some c4834, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8102 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8102 : lratChecker f8102 p8102 = .success := by decide +kernel
theorem unsat8102 : Unsatisfiable (PosFin 65) f8102 := by
  apply lratCheckerSound f8102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8102
  · intro a ha; simp [p8102] at ha; subst a; trivial
  · exact checked8102
theorem derived8102 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8102 := by
  apply localUnsat_implies_entails f8102 [c1498, c1556, c1655, c4834] c8102 unsat8102 (by rfl) a
  have h0 : Entails.eval a c1498 := h 1497 (by decide)
  have h1 : Entails.eval a c1556 := h 1555 (by decide)
  have h2 : Entails.eval a c1655 := h 1654 (by decide)
  have h3 : Entails.eval a c4834 := h 4833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8103 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8103 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c521, some c519, some c3113, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8103 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8103 : lratChecker f8103 p8103 = .success := by decide +kernel
theorem unsat8103 : Unsatisfiable (PosFin 65) f8103 := by
  apply lratCheckerSound f8103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8103
  · intro a ha; simp [p8103] at ha; subst a; trivial
  · exact checked8103
theorem derived8103 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8103 := by
  apply localUnsat_implies_entails f8103 [c521, c519, c3113] c8103 unsat8103 (by rfl) a
  have h0 : Entails.eval a c521 := h 520 (by decide)
  have h1 : Entails.eval a c519 := h 518 (by decide)
  have h2 : Entails.eval a c3113 := h 3112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8104 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8104 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6299, some c6315, some c7306, some c7409, some c7268, some c6719, some c7274, some c7213, some c7472, some c8101, some c8103, some c8102, some c412, some c2424, some c2470, some c2507, some c3782, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8104 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8104 : lratChecker f8104 p8104 = .success := by decide +kernel
theorem unsat8104 : Unsatisfiable (PosFin 65) f8104 := by
  apply lratCheckerSound f8104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8104
  · intro a ha; simp [p8104] at ha; subst a; trivial
  · exact checked8104
theorem derived8104 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8104 := by
  apply localUnsat_implies_entails f8104 [c6299, c6315, c7306, c7409, c7268, c6719, c7274, c7213, c7472, c8101, c8103, c8102, c412, c2424, c2470, c2507, c3782] c8104 unsat8104 (by rfl) a
  have h0 : Entails.eval a c6299 := h 6298 (by decide)
  have h1 : Entails.eval a c6315 := h 6314 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7268 := h 7267 (by decide)
  have h5 : Entails.eval a c6719 := h 6718 (by decide)
  have h6 : Entails.eval a c7274 := h 7273 (by decide)
  have h7 : Entails.eval a c7213 := h 7212 (by decide)
  have h8 : Entails.eval a c7472 := h 7471 (by decide)
  have h9 : Entails.eval a c8101 := derived8101 a h
  have h10 : Entails.eval a c8103 := derived8103 a h
  have h11 : Entails.eval a c8102 := derived8102 a h
  have h12 : Entails.eval a c412 := h 411 (by decide)
  have h13 : Entails.eval a c2424 := h 2423 (by decide)
  have h14 : Entails.eval a c2470 := h 2469 (by decide)
  have h15 : Entails.eval a c2507 := h 2506 (by decide)
  have h16 : Entails.eval a c3782 := h 3781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8105 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨58, by decide⟩, false), (⟨61, by decide⟩, false), (⟨54, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8105 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c424, some c435, some c412, some c2411, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8105 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8105 : lratChecker f8105 p8105 = .success := by decide +kernel
theorem unsat8105 : Unsatisfiable (PosFin 65) f8105 := by
  apply lratCheckerSound f8105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8105
  · intro a ha; simp [p8105] at ha; subst a; trivial
  · exact checked8105
theorem derived8105 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8105 := by
  apply localUnsat_implies_entails f8105 [c424, c435, c412, c2411] c8105 unsat8105 (by rfl) a
  have h0 : Entails.eval a c424 := h 423 (by decide)
  have h1 : Entails.eval a c435 := h 434 (by decide)
  have h2 : Entails.eval a c412 := h 411 (by decide)
  have h3 : Entails.eval a c2411 := h 2410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8106 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨58, by decide⟩, false), (⟨61, by decide⟩, false), (⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8106 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1656, some c1557, some c1498, some c4839, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8106 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8106 : lratChecker f8106 p8106 = .success := by decide +kernel
theorem unsat8106 : Unsatisfiable (PosFin 65) f8106 := by
  apply lratCheckerSound f8106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8106
  · intro a ha; simp [p8106] at ha; subst a; trivial
  · exact checked8106
theorem derived8106 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8106 := by
  apply localUnsat_implies_entails f8106 [c1656, c1557, c1498, c4839] c8106 unsat8106 (by rfl) a
  have h0 : Entails.eval a c1656 := h 1655 (by decide)
  have h1 : Entails.eval a c1557 := h 1556 (by decide)
  have h2 : Entails.eval a c1498 := h 1497 (by decide)
  have h3 : Entails.eval a c4839 := h 4838 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8107 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8107 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c466, some c8103, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8107 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8107 : lratChecker f8107 p8107 = .success := by decide +kernel
theorem unsat8107 : Unsatisfiable (PosFin 65) f8107 := by
  apply lratCheckerSound f8107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8107
  · intro a ha; simp [p8107] at ha; subst a; trivial
  · exact checked8107
theorem derived8107 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8107 := by
  apply localUnsat_implies_entails f8107 [c466, c8103] c8107 unsat8107 (by rfl) a
  have h0 : Entails.eval a c466 := h 465 (by decide)
  have h1 : Entails.eval a c8103 := derived8103 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8108 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨61, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8108 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8106, some c1557, some c1498, some c1655, some c4826, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8108 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8108 : lratChecker f8108 p8108 = .success := by decide +kernel
theorem unsat8108 : Unsatisfiable (PosFin 65) f8108 := by
  apply lratCheckerSound f8108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8108
  · intro a ha; simp [p8108] at ha; subst a; trivial
  · exact checked8108
theorem derived8108 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8108 := by
  apply localUnsat_implies_entails f8108 [c8106, c1557, c1498, c1655, c4826] c8108 unsat8108 (by rfl) a
  have h0 : Entails.eval a c8106 := derived8106 a h
  have h1 : Entails.eval a c1557 := h 1556 (by decide)
  have h2 : Entails.eval a c1498 := h 1497 (by decide)
  have h3 : Entails.eval a c1655 := h 1654 (by decide)
  have h4 : Entails.eval a c4826 := h 4825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8109 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨36, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8109 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6315, some c6299, some c7306, some c7409, some c7268, some c7274, some c7472, some c7213, some c8107, some c6719, some c8108, some c412, some c417, some c8105, some c2424, some c430, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8109 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8109 : lratChecker f8109 p8109 = .success := by decide +kernel
theorem unsat8109 : Unsatisfiable (PosFin 65) f8109 := by
  apply lratCheckerSound f8109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8109
  · intro a ha; simp [p8109] at ha; subst a; trivial
  · exact checked8109
theorem derived8109 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8109 := by
  apply localUnsat_implies_entails f8109 [c6315, c6299, c7306, c7409, c7268, c7274, c7472, c7213, c8107, c6719, c8108, c412, c417, c8105, c2424, c430] c8109 unsat8109 (by rfl) a
  have h0 : Entails.eval a c6315 := h 6314 (by decide)
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7268 := h 7267 (by decide)
  have h5 : Entails.eval a c7274 := h 7273 (by decide)
  have h6 : Entails.eval a c7472 := h 7471 (by decide)
  have h7 : Entails.eval a c7213 := h 7212 (by decide)
  have h8 : Entails.eval a c8107 := derived8107 a h
  have h9 : Entails.eval a c6719 := h 6718 (by decide)
  have h10 : Entails.eval a c8108 := derived8108 a h
  have h11 : Entails.eval a c412 := h 411 (by decide)
  have h12 : Entails.eval a c417 := h 416 (by decide)
  have h13 : Entails.eval a c8105 := derived8105 a h
  have h14 : Entails.eval a c2424 := h 2423 (by decide)
  have h15 : Entails.eval a c430 := h 429 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8110 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨61, by decide⟩, true), (⟨49, by decide⟩, true), (⟨36, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8110 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6299, some c6315, some c7306, some c7409, some c7268, some c6719, some c412, some c417, some c433, some c2422, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8110 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8110 : lratChecker f8110 p8110 = .success := by decide +kernel
theorem unsat8110 : Unsatisfiable (PosFin 65) f8110 := by
  apply lratCheckerSound f8110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8110
  · intro a ha; simp [p8110] at ha; subst a; trivial
  · exact checked8110
theorem derived8110 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8110 := by
  apply localUnsat_implies_entails f8110 [c6299, c6315, c7306, c7409, c7268, c6719, c412, c417, c433, c2422] c8110 unsat8110 (by rfl) a
  have h0 : Entails.eval a c6299 := h 6298 (by decide)
  have h1 : Entails.eval a c6315 := h 6314 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7268 := h 7267 (by decide)
  have h5 : Entails.eval a c6719 := h 6718 (by decide)
  have h6 : Entails.eval a c412 := h 411 (by decide)
  have h7 : Entails.eval a c417 := h 416 (by decide)
  have h8 : Entails.eval a c433 := h 432 (by decide)
  have h9 : Entails.eval a c2422 := h 2421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8111 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨36, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8111 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6315, some c6299, some c7306, some c7409, some c7274, some c7268, some c7213, some c7472, some c8104, some c8107, some c8109, some c8110, some c1557, some c1498, some c1655, some c4824, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8111 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8111 : lratChecker f8111 p8111 = .success := by decide +kernel
theorem unsat8111 : Unsatisfiable (PosFin 65) f8111 := by
  apply lratCheckerSound f8111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8111
  · intro a ha; simp [p8111] at ha; subst a; trivial
  · exact checked8111
theorem derived8111 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8111 := by
  apply localUnsat_implies_entails f8111 [c6315, c6299, c7306, c7409, c7274, c7268, c7213, c7472, c8104, c8107, c8109, c8110, c1557, c1498, c1655, c4824] c8111 unsat8111 (by rfl) a
  have h0 : Entails.eval a c6315 := h 6314 (by decide)
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7274 := h 7273 (by decide)
  have h5 : Entails.eval a c7268 := h 7267 (by decide)
  have h6 : Entails.eval a c7213 := h 7212 (by decide)
  have h7 : Entails.eval a c7472 := h 7471 (by decide)
  have h8 : Entails.eval a c8104 := derived8104 a h
  have h9 : Entails.eval a c8107 := derived8107 a h
  have h10 : Entails.eval a c8109 := derived8109 a h
  have h11 : Entails.eval a c8110 := derived8110 a h
  have h12 : Entails.eval a c1557 := h 1556 (by decide)
  have h13 : Entails.eval a c1498 := h 1497 (by decide)
  have h14 : Entails.eval a c1655 := h 1654 (by decide)
  have h15 : Entails.eval a c4824 := h 4823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8112 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8112 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6315, some c6299, some c7306, some c7409, some c1557, some c1498, some c1655, some c4813, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8112 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8112 : lratChecker f8112 p8112 = .success := by decide +kernel
theorem unsat8112 : Unsatisfiable (PosFin 65) f8112 := by
  apply lratCheckerSound f8112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8112
  · intro a ha; simp [p8112] at ha; subst a; trivial
  · exact checked8112
theorem derived8112 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8112 := by
  apply localUnsat_implies_entails f8112 [c6315, c6299, c7306, c7409, c1557, c1498, c1655, c4813] c8112 unsat8112 (by rfl) a
  have h0 : Entails.eval a c6315 := h 6314 (by decide)
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c1557 := h 1556 (by decide)
  have h5 : Entails.eval a c1498 := h 1497 (by decide)
  have h6 : Entails.eval a c1655 := h 1654 (by decide)
  have h7 : Entails.eval a c4813 := h 4812 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8113 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8113 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6315, some c6299, some c7306, some c7409, some c7274, some c7268, some c7213, some c7472, some c8112, some c513, some c521, some c1744, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8113 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8113 : lratChecker f8113 p8113 = .success := by decide +kernel
theorem unsat8113 : Unsatisfiable (PosFin 65) f8113 := by
  apply lratCheckerSound f8113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8113
  · intro a ha; simp [p8113] at ha; subst a; trivial
  · exact checked8113
theorem derived8113 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8113 := by
  apply localUnsat_implies_entails f8113 [c6315, c6299, c7306, c7409, c7274, c7268, c7213, c7472, c8112, c513, c521, c1744] c8113 unsat8113 (by rfl) a
  have h0 : Entails.eval a c6315 := h 6314 (by decide)
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7274 := h 7273 (by decide)
  have h5 : Entails.eval a c7268 := h 7267 (by decide)
  have h6 : Entails.eval a c7213 := h 7212 (by decide)
  have h7 : Entails.eval a c7472 := h 7471 (by decide)
  have h8 : Entails.eval a c8112 := derived8112 a h
  have h9 : Entails.eval a c513 := h 512 (by decide)
  have h10 : Entails.eval a c521 := h 520 (by decide)
  have h11 : Entails.eval a c1744 := h 1743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8114 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8114 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6315, some c6299, some c7306, some c7409, some c7274, some c7268, some c7213, some c7126, some c8100, some c8111, some c6719, some c8113, some c412, some c417, some c2411, some c2468, some c2510, some c3782, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8114 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8114 : lratChecker f8114 p8114 = .success := by decide +kernel
theorem unsat8114 : Unsatisfiable (PosFin 65) f8114 := by
  apply lratCheckerSound f8114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8114
  · intro a ha; simp [p8114] at ha; subst a; trivial
  · exact checked8114
theorem derived8114 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8114 := by
  apply localUnsat_implies_entails f8114 [c6315, c6299, c7306, c7409, c7274, c7268, c7213, c7126, c8100, c8111, c6719, c8113, c412, c417, c2411, c2468, c2510, c3782] c8114 unsat8114 (by rfl) a
  have h0 : Entails.eval a c6315 := h 6314 (by decide)
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7274 := h 7273 (by decide)
  have h5 : Entails.eval a c7268 := h 7267 (by decide)
  have h6 : Entails.eval a c7213 := h 7212 (by decide)
  have h7 : Entails.eval a c7126 := h 7125 (by decide)
  have h8 : Entails.eval a c8100 := derived8100 a h
  have h9 : Entails.eval a c8111 := derived8111 a h
  have h10 : Entails.eval a c6719 := h 6718 (by decide)
  have h11 : Entails.eval a c8113 := derived8113 a h
  have h12 : Entails.eval a c412 := h 411 (by decide)
  have h13 : Entails.eval a c417 := h 416 (by decide)
  have h14 : Entails.eval a c2411 := h 2410 (by decide)
  have h15 : Entails.eval a c2468 := h 2467 (by decide)
  have h16 : Entails.eval a c2510 := h 2509 (by decide)
  have h17 : Entails.eval a c3782 := h 3781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8115 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8115 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c412, some c2476, some c2112, some c2162, some c1353, some c3718, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8115 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8115 : lratChecker f8115 p8115 = .success := by decide +kernel
theorem unsat8115 : Unsatisfiable (PosFin 65) f8115 := by
  apply lratCheckerSound f8115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8115
  · intro a ha; simp [p8115] at ha; subst a; trivial
  · exact checked8115
theorem derived8115 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8115 := by
  apply localUnsat_implies_entails f8115 [c412, c2476, c2112, c2162, c1353, c3718] c8115 unsat8115 (by rfl) a
  have h0 : Entails.eval a c412 := h 411 (by decide)
  have h1 : Entails.eval a c2476 := h 2475 (by decide)
  have h2 : Entails.eval a c2112 := h 2111 (by decide)
  have h3 : Entails.eval a c2162 := h 2161 (by decide)
  have h4 : Entails.eval a c1353 := h 1352 (by decide)
  have h5 : Entails.eval a c3718 := h 3717 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8116 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8116 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6315, some c6299, some c7306, some c7409, some c7274, some c7268, some c7213, some c7126, some c6719, some c7472, some c8100, some c8111, some c8114, some c8101, some c8115, some c8102, some c513, some c521, some c1744, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8116 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8116 : lratChecker f8116 p8116 = .success := by decide +kernel
theorem unsat8116 : Unsatisfiable (PosFin 65) f8116 := by
  apply lratCheckerSound f8116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8116
  · intro a ha; simp [p8116] at ha; subst a; trivial
  · exact checked8116
theorem derived8116 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8116 := by
  apply localUnsat_implies_entails f8116 [c6315, c6299, c7306, c7409, c7274, c7268, c7213, c7126, c6719, c7472, c8100, c8111, c8114, c8101, c8115, c8102, c513, c521, c1744] c8116 unsat8116 (by rfl) a
  have h0 : Entails.eval a c6315 := h 6314 (by decide)
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7274 := h 7273 (by decide)
  have h5 : Entails.eval a c7268 := h 7267 (by decide)
  have h6 : Entails.eval a c7213 := h 7212 (by decide)
  have h7 : Entails.eval a c7126 := h 7125 (by decide)
  have h8 : Entails.eval a c6719 := h 6718 (by decide)
  have h9 : Entails.eval a c7472 := h 7471 (by decide)
  have h10 : Entails.eval a c8100 := derived8100 a h
  have h11 : Entails.eval a c8111 := derived8111 a h
  have h12 : Entails.eval a c8114 := derived8114 a h
  have h13 : Entails.eval a c8101 := derived8101 a h
  have h14 : Entails.eval a c8115 := derived8115 a h
  have h15 : Entails.eval a c8102 := derived8102 a h
  have h16 : Entails.eval a c513 := h 512 (by decide)
  have h17 : Entails.eval a c521 := h 520 (by decide)
  have h18 : Entails.eval a c1744 := h 1743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8117 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨1, by decide⟩, true), (⟨51, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8117 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c521, some c519, some c1724, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8117 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8117 : lratChecker f8117 p8117 = .success := by decide +kernel
theorem unsat8117 : Unsatisfiable (PosFin 65) f8117 := by
  apply lratCheckerSound f8117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8117
  · intro a ha; simp [p8117] at ha; subst a; trivial
  · exact checked8117
theorem derived8117 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8117 := by
  apply localUnsat_implies_entails f8117 [c521, c519, c1724] c8117 unsat8117 (by rfl) a
  have h0 : Entails.eval a c521 := h 520 (by decide)
  have h1 : Entails.eval a c519 := h 518 (by decide)
  have h2 : Entails.eval a c1724 := h 1723 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8118 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8118 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8117, some c1560, some c1506, some c1655, some c4834, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8118 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8118 : lratChecker f8118 p8118 = .success := by decide +kernel
theorem unsat8118 : Unsatisfiable (PosFin 65) f8118 := by
  apply lratCheckerSound f8118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8118
  · intro a ha; simp [p8118] at ha; subst a; trivial
  · exact checked8118
theorem derived8118 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8118 := by
  apply localUnsat_implies_entails f8118 [c8117, c1560, c1506, c1655, c4834] c8118 unsat8118 (by rfl) a
  have h0 : Entails.eval a c8117 := derived8117 a h
  have h1 : Entails.eval a c1560 := h 1559 (by decide)
  have h2 : Entails.eval a c1506 := h 1505 (by decide)
  have h3 : Entails.eval a c1655 := h 1654 (by decide)
  have h4 : Entails.eval a c4834 := h 4833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8119 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8119 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6299, some c6315, some c7306, some c7409, some c7268, some c6719, some c7274, some c7213, some c7472, some c8075, some c8101, some c8118, some c8, some c412, some c2476, some c2510, some c2112, some c2168, some c4417, some c3250, some c4617, some c4468, some c3134, some c89, some c74, some c1053, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8119 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked8119 : lratChecker f8119 p8119 = .success := by decide +kernel
theorem unsat8119 : Unsatisfiable (PosFin 65) f8119 := by
  apply lratCheckerSound f8119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8119
  · intro a ha; simp [p8119] at ha; subst a; trivial
  · exact checked8119
theorem derived8119 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8119 := by
  apply localUnsat_implies_entails f8119 [c7994, c6299, c6315, c7306, c7409, c7268, c6719, c7274, c7213, c7472, c8075, c8101, c8118, c8, c412, c2476, c2510, c2112, c2168, c4417, c3250, c4617, c4468, c3134, c89, c74, c1053] c8119 unsat8119 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c6315 := h 6314 (by decide)
  have h3 : Entails.eval a c7306 := h 7305 (by decide)
  have h4 : Entails.eval a c7409 := h 7408 (by decide)
  have h5 : Entails.eval a c7268 := h 7267 (by decide)
  have h6 : Entails.eval a c6719 := h 6718 (by decide)
  have h7 : Entails.eval a c7274 := h 7273 (by decide)
  have h8 : Entails.eval a c7213 := h 7212 (by decide)
  have h9 : Entails.eval a c7472 := h 7471 (by decide)
  have h10 : Entails.eval a c8075 := derived8075 a h
  have h11 : Entails.eval a c8101 := derived8101 a h
  have h12 : Entails.eval a c8118 := derived8118 a h
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c412 := h 411 (by decide)
  have h15 : Entails.eval a c2476 := h 2475 (by decide)
  have h16 : Entails.eval a c2510 := h 2509 (by decide)
  have h17 : Entails.eval a c2112 := h 2111 (by decide)
  have h18 : Entails.eval a c2168 := h 2167 (by decide)
  have h19 : Entails.eval a c4417 := h 4416 (by decide)
  have h20 : Entails.eval a c3250 := h 3249 (by decide)
  have h21 : Entails.eval a c4617 := h 4616 (by decide)
  have h22 : Entails.eval a c4468 := h 4467 (by decide)
  have h23 : Entails.eval a c3134 := h 3133 (by decide)
  have h24 : Entails.eval a c89 := h 88 (by decide)
  have h25 : Entails.eval a c74 := h 73 (by decide)
  have h26 : Entails.eval a c1053 := h 1052 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8120 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8120 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6299, some c6315, some c7306, some c7409, some c7268, some c6719, some c412, some c417, some c2411, some c2468, some c2510, some c3783, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8120 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8120 : lratChecker f8120 p8120 = .success := by decide +kernel
theorem unsat8120 : Unsatisfiable (PosFin 65) f8120 := by
  apply lratCheckerSound f8120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8120
  · intro a ha; simp [p8120] at ha; subst a; trivial
  · exact checked8120
theorem derived8120 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8120 := by
  apply localUnsat_implies_entails f8120 [c6299, c6315, c7306, c7409, c7268, c6719, c412, c417, c2411, c2468, c2510, c3783] c8120 unsat8120 (by rfl) a
  have h0 : Entails.eval a c6299 := h 6298 (by decide)
  have h1 : Entails.eval a c6315 := h 6314 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7268 := h 7267 (by decide)
  have h5 : Entails.eval a c6719 := h 6718 (by decide)
  have h6 : Entails.eval a c412 := h 411 (by decide)
  have h7 : Entails.eval a c417 := h 416 (by decide)
  have h8 : Entails.eval a c2411 := h 2410 (by decide)
  have h9 : Entails.eval a c2468 := h 2467 (by decide)
  have h10 : Entails.eval a c2510 := h 2509 (by decide)
  have h11 : Entails.eval a c3783 := h 3782 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8121 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8121 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6315, some c6299, some c7306, some c7409, some c7274, some c7994, some c7268, some c7213, some c7472, some c8075, some c8116, some c8119, some c8120, some c8117, some c1560, some c1496, some c1655, some c4824, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8121 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8121 : lratChecker f8121 p8121 = .success := by decide +kernel
theorem unsat8121 : Unsatisfiable (PosFin 65) f8121 := by
  apply lratCheckerSound f8121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8121
  · intro a ha; simp [p8121] at ha; subst a; trivial
  · exact checked8121
theorem derived8121 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8121 := by
  apply localUnsat_implies_entails f8121 [c6315, c6299, c7306, c7409, c7274, c7994, c7268, c7213, c7472, c8075, c8116, c8119, c8120, c8117, c1560, c1496, c1655, c4824] c8121 unsat8121 (by rfl) a
  have h0 : Entails.eval a c6315 := h 6314 (by decide)
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c7306 := h 7305 (by decide)
  have h3 : Entails.eval a c7409 := h 7408 (by decide)
  have h4 : Entails.eval a c7274 := h 7273 (by decide)
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c7268 := h 7267 (by decide)
  have h7 : Entails.eval a c7213 := h 7212 (by decide)
  have h8 : Entails.eval a c7472 := h 7471 (by decide)
  have h9 : Entails.eval a c8075 := derived8075 a h
  have h10 : Entails.eval a c8116 := derived8116 a h
  have h11 : Entails.eval a c8119 := derived8119 a h
  have h12 : Entails.eval a c8120 := derived8120 a h
  have h13 : Entails.eval a c8117 := derived8117 a h
  have h14 : Entails.eval a c1560 := h 1559 (by decide)
  have h15 : Entails.eval a c1496 := h 1495 (by decide)
  have h16 : Entails.eval a c1655 := h 1654 (by decide)
  have h17 : Entails.eval a c4824 := h 4823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8122 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨1, by decide⟩, true), (⟨63, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8122 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8117, some c1560, some c1496, some c1655, some c4825, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8122 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8122 : lratChecker f8122 p8122 = .success := by decide +kernel
theorem unsat8122 : Unsatisfiable (PosFin 65) f8122 := by
  apply lratCheckerSound f8122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8122
  · intro a ha; simp [p8122] at ha; subst a; trivial
  · exact checked8122
theorem derived8122 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8122 := by
  apply localUnsat_implies_entails f8122 [c8117, c1560, c1496, c1655, c4825] c8122 unsat8122 (by rfl) a
  have h0 : Entails.eval a c8117 := derived8117 a h
  have h1 : Entails.eval a c1560 := h 1559 (by decide)
  have h2 : Entails.eval a c1496 := h 1495 (by decide)
  have h3 : Entails.eval a c1655 := h 1654 (by decide)
  have h4 : Entails.eval a c4825 := h 4824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8123 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨36, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8123 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c533, some c475, some c495, some c2957, some c2952, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8123 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8123 : lratChecker f8123 p8123 = .success := by decide +kernel
theorem unsat8123 : Unsatisfiable (PosFin 65) f8123 := by
  apply lratCheckerSound f8123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8123
  · intro a ha; simp [p8123] at ha; subst a; trivial
  · exact checked8123
theorem derived8123 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8123 := by
  apply localUnsat_implies_entails f8123 [c533, c475, c495, c2957, c2952] c8123 unsat8123 (by rfl) a
  have h0 : Entails.eval a c533 := h 532 (by decide)
  have h1 : Entails.eval a c475 := h 474 (by decide)
  have h2 : Entails.eval a c495 := h 494 (by decide)
  have h3 : Entails.eval a c2957 := h 2956 (by decide)
  have h4 : Entails.eval a c2952 := h 2951 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8124 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8124 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7274, some c7268, some c7213, some c7126, some c7472, some c8122, some c7077, some c8123, some c1521, some c1953, some c521, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8124 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8124 : lratChecker f8124 p8124 = .success := by decide +kernel
theorem unsat8124 : Unsatisfiable (PosFin 65) f8124 := by
  apply lratCheckerSound f8124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8124
  · intro a ha; simp [p8124] at ha; subst a; trivial
  · exact checked8124
theorem derived8124 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8124 := by
  apply localUnsat_implies_entails f8124 [c7274, c7268, c7213, c7126, c7472, c8122, c7077, c8123, c1521, c1953, c521] c8124 unsat8124 (by rfl) a
  have h0 : Entails.eval a c7274 := h 7273 (by decide)
  have h1 : Entails.eval a c7268 := h 7267 (by decide)
  have h2 : Entails.eval a c7213 := h 7212 (by decide)
  have h3 : Entails.eval a c7126 := h 7125 (by decide)
  have h4 : Entails.eval a c7472 := h 7471 (by decide)
  have h5 : Entails.eval a c8122 := derived8122 a h
  have h6 : Entails.eval a c7077 := h 7076 (by decide)
  have h7 : Entails.eval a c8123 := derived8123 a h
  have h8 : Entails.eval a c1521 := h 1520 (by decide)
  have h9 : Entails.eval a c1953 := h 1952 (by decide)
  have h10 : Entails.eval a c521 := h 520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8125 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8125 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c7994, some c6315, some c6299, some c7409, some c7306, some c7274, some c7268, some c7472, some c6719, some c8121, some c8124, some c10, some c412, some c417, some c2483, some c2112, some c2164, some c3254, some c4620, some c89, some c81, some c5418, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8125 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8125 : lratChecker f8125 p8125 = .success := by decide +kernel
theorem unsat8125 : Unsatisfiable (PosFin 65) f8125 := by
  apply lratCheckerSound f8125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8125
  · intro a ha; simp [p8125] at ha; subst a; trivial
  · exact checked8125
theorem derived8125 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8125 := by
  apply localUnsat_implies_entails f8125 [c8075, c7994, c6315, c6299, c7409, c7306, c7274, c7268, c7472, c6719, c8121, c8124, c10, c412, c417, c2483, c2112, c2164, c3254, c4620, c89, c81, c5418] c8125 unsat8125 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c6315 := h 6314 (by decide)
  have h3 : Entails.eval a c6299 := h 6298 (by decide)
  have h4 : Entails.eval a c7409 := h 7408 (by decide)
  have h5 : Entails.eval a c7306 := h 7305 (by decide)
  have h6 : Entails.eval a c7274 := h 7273 (by decide)
  have h7 : Entails.eval a c7268 := h 7267 (by decide)
  have h8 : Entails.eval a c7472 := h 7471 (by decide)
  have h9 : Entails.eval a c6719 := h 6718 (by decide)
  have h10 : Entails.eval a c8121 := derived8121 a h
  have h11 : Entails.eval a c8124 := derived8124 a h
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c412 := h 411 (by decide)
  have h14 : Entails.eval a c417 := h 416 (by decide)
  have h15 : Entails.eval a c2483 := h 2482 (by decide)
  have h16 : Entails.eval a c2112 := h 2111 (by decide)
  have h17 : Entails.eval a c2164 := h 2163 (by decide)
  have h18 : Entails.eval a c3254 := h 3253 (by decide)
  have h19 : Entails.eval a c4620 := h 4619 (by decide)
  have h20 : Entails.eval a c89 := h 88 (by decide)
  have h21 : Entails.eval a c81 := h 80 (by decide)
  have h22 : Entails.eval a c5418 := h 5417 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8126 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨7, by decide⟩, false), (⟨40, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, true), (⟨38, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8126 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c536, some c80, some c3119, some c5417, some c87, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8126 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8126 : lratChecker f8126 p8126 = .success := by decide +kernel
theorem unsat8126 : Unsatisfiable (PosFin 65) f8126 := by
  apply lratCheckerSound f8126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8126
  · intro a ha; simp [p8126] at ha; subst a; trivial
  · exact checked8126
theorem derived8126 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8126 := by
  apply localUnsat_implies_entails f8126 [c536, c80, c3119, c5417, c87] c8126 unsat8126 (by rfl) a
  have h0 : Entails.eval a c536 := h 535 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c3119 := h 3118 (by decide)
  have h3 : Entails.eval a c5417 := h 5416 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8127 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨44, by decide⟩, true), (⟨52, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8127 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6676, some c7386, some c6646, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8127 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8127 : lratChecker f8127 p8127 = .success := by decide +kernel
theorem unsat8127 : Unsatisfiable (PosFin 65) f8127 := by
  apply lratCheckerSound f8127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8127
  · intro a ha; simp [p8127] at ha; subst a; trivial
  · exact checked8127
theorem derived8127 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8127 := by
  apply localUnsat_implies_entails f8127 [c6676, c7386, c6646] c8127 unsat8127 (by rfl) a
  have h0 : Entails.eval a c6676 := h 6675 (by decide)
  have h1 : Entails.eval a c7386 := h 7385 (by decide)
  have h2 : Entails.eval a c6646 := h 6645 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8128 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8128 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c458, some c451, some c3116, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8128 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8128 : lratChecker f8128 p8128 = .success := by decide +kernel
theorem unsat8128 : Unsatisfiable (PosFin 65) f8128 := by
  apply lratCheckerSound f8128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8128
  · intro a ha; simp [p8128] at ha; subst a; trivial
  · exact checked8128
theorem derived8128 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8128 := by
  apply localUnsat_implies_entails f8128 [c458, c451, c3116] c8128 unsat8128 (by rfl) a
  have h0 : Entails.eval a c458 := h 457 (by decide)
  have h1 : Entails.eval a c451 := h 450 (by decide)
  have h2 : Entails.eval a c3116 := h 3115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8129 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8129 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8128, some c2587, some c518, some c523, some c3119, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8129 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8129 : lratChecker f8129 p8129 = .success := by decide +kernel
theorem unsat8129 : Unsatisfiable (PosFin 65) f8129 := by
  apply lratCheckerSound f8129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8129
  · intro a ha; simp [p8129] at ha; subst a; trivial
  · exact checked8129
theorem derived8129 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8129 := by
  apply localUnsat_implies_entails f8129 [c8128, c2587, c518, c523, c3119] c8129 unsat8129 (by rfl) a
  have h0 : Entails.eval a c8128 := derived8128 a h
  have h1 : Entails.eval a c2587 := h 2586 (by decide)
  have h2 : Entails.eval a c518 := h 517 (by decide)
  have h3 : Entails.eval a c523 := h 522 (by decide)
  have h4 : Entails.eval a c3119 := h 3118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8130 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8130 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6320, some c6305, some c7312, some c8129, some c421, some c470, some c1520, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8130 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8130 : lratChecker f8130 p8130 = .success := by decide +kernel
theorem unsat8130 : Unsatisfiable (PosFin 65) f8130 := by
  apply lratCheckerSound f8130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8130
  · intro a ha; simp [p8130] at ha; subst a; trivial
  · exact checked8130
theorem derived8130 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8130 := by
  apply localUnsat_implies_entails f8130 [c6320, c6305, c7312, c8129, c421, c470, c1520] c8130 unsat8130 (by rfl) a
  have h0 : Entails.eval a c6320 := h 6319 (by decide)
  have h1 : Entails.eval a c6305 := h 6304 (by decide)
  have h2 : Entails.eval a c7312 := h 7311 (by decide)
  have h3 : Entails.eval a c8129 := derived8129 a h
  have h4 : Entails.eval a c421 := h 420 (by decide)
  have h5 : Entails.eval a c470 := h 469 (by decide)
  have h6 : Entails.eval a c1520 := h 1519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8131 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8131 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8094, some c8075, some c8099, some c8125, some c6320, some c6305, some c7312, some c8127, some c6863, some c7267, some c7219, some c6717, some c7478, some c8130, some c536, some c480, some c8126, some c8128, some c9, some c2478, some c1799, some c4686, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8131 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8131 : lratChecker f8131 p8131 = .success := by decide +kernel
theorem unsat8131 : Unsatisfiable (PosFin 65) f8131 := by
  apply lratCheckerSound f8131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8131
  · intro a ha; simp [p8131] at ha; subst a; trivial
  · exact checked8131
theorem derived8131 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8131 := by
  apply localUnsat_implies_entails f8131 [c8094, c8075, c8099, c8125, c6320, c6305, c7312, c8127, c6863, c7267, c7219, c6717, c7478, c8130, c536, c480, c8126, c8128, c9, c2478, c1799, c4686] c8131 unsat8131 (by rfl) a
  have h0 : Entails.eval a c8094 := derived8094 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c8099 := derived8099 a h
  have h3 : Entails.eval a c8125 := derived8125 a h
  have h4 : Entails.eval a c6320 := h 6319 (by decide)
  have h5 : Entails.eval a c6305 := h 6304 (by decide)
  have h6 : Entails.eval a c7312 := h 7311 (by decide)
  have h7 : Entails.eval a c8127 := derived8127 a h
  have h8 : Entails.eval a c6863 := h 6862 (by decide)
  have h9 : Entails.eval a c7267 := h 7266 (by decide)
  have h10 : Entails.eval a c7219 := h 7218 (by decide)
  have h11 : Entails.eval a c6717 := h 6716 (by decide)
  have h12 : Entails.eval a c7478 := h 7477 (by decide)
  have h13 : Entails.eval a c8130 := derived8130 a h
  have h14 : Entails.eval a c536 := h 535 (by decide)
  have h15 : Entails.eval a c480 := h 479 (by decide)
  have h16 : Entails.eval a c8126 := derived8126 a h
  have h17 : Entails.eval a c8128 := derived8128 a h
  have h18 : Entails.eval a c9 := h 8 (by decide)
  have h19 : Entails.eval a c2478 := h 2477 (by decide)
  have h20 : Entails.eval a c1799 := h 1798 (by decide)
  have h21 : Entails.eval a c4686 := h 4685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8132 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8132 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8131, some c8094, some c8075, some c7994, some c6909, some c6597, some c6646, some c6278, some c8095, some c8096, some c6695, some c6691, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8132 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8132 : lratChecker f8132 p8132 = .success := by decide +kernel
theorem unsat8132 : Unsatisfiable (PosFin 65) f8132 := by
  apply lratCheckerSound f8132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8132
  · intro a ha; simp [p8132] at ha; subst a; trivial
  · exact checked8132
theorem derived8132 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8132 := by
  apply localUnsat_implies_entails f8132 [c8131, c8094, c8075, c7994, c6909, c6597, c6646, c6278, c8095, c8096, c6695, c6691] c8132 unsat8132 (by rfl) a
  have h0 : Entails.eval a c8131 := derived8131 a h
  have h1 : Entails.eval a c8094 := derived8094 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c6909 := h 6908 (by decide)
  have h5 : Entails.eval a c6597 := h 6596 (by decide)
  have h6 : Entails.eval a c6646 := h 6645 (by decide)
  have h7 : Entails.eval a c6278 := h 6277 (by decide)
  have h8 : Entails.eval a c8095 := derived8095 a h
  have h9 : Entails.eval a c8096 := derived8096 a h
  have h10 : Entails.eval a c6695 := h 6694 (by decide)
  have h11 : Entails.eval a c6691 := h 6690 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8133 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8133 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8094, some c8131, some c8132, some c6953, some c6904, some c6598, some c6707, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8133 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8133 : lratChecker f8133 p8133 = .success := by decide +kernel
theorem unsat8133 : Unsatisfiable (PosFin 65) f8133 := by
  apply lratCheckerSound f8133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8133
  · intro a ha; simp [p8133] at ha; subst a; trivial
  · exact checked8133
theorem derived8133 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8133 := by
  apply localUnsat_implies_entails f8133 [c7994, c8094, c8131, c8132, c6953, c6904, c6598, c6707] c8133 unsat8133 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8094 := derived8094 a h
  have h2 : Entails.eval a c8131 := derived8131 a h
  have h3 : Entails.eval a c8132 := derived8132 a h
  have h4 : Entails.eval a c6953 := h 6952 (by decide)
  have h5 : Entails.eval a c6904 := h 6903 (by decide)
  have h6 : Entails.eval a c6598 := h 6597 (by decide)
  have h7 : Entails.eval a c6707 := h 6706 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8134 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨34, by decide⟩, false), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8134 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6707, some c6648, some c6844, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8134 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8134 : lratChecker f8134 p8134 = .success := by decide +kernel
theorem unsat8134 : Unsatisfiable (PosFin 65) f8134 := by
  apply lratCheckerSound f8134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8134
  · intro a ha; simp [p8134] at ha; subst a; trivial
  · exact checked8134
theorem derived8134 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8134 := by
  apply localUnsat_implies_entails f8134 [c6707, c6648, c6844] c8134 unsat8134 (by rfl) a
  have h0 : Entails.eval a c6707 := h 6706 (by decide)
  have h1 : Entails.eval a c6648 := h 6647 (by decide)
  have h2 : Entails.eval a c6844 := h 6843 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8135 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨45, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8135 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8134, some c6880, some c6698, some c7168, some c7488, some c7249, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8135 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8135 : lratChecker f8135 p8135 = .success := by decide +kernel
theorem unsat8135 : Unsatisfiable (PosFin 65) f8135 := by
  apply lratCheckerSound f8135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8135
  · intro a ha; simp [p8135] at ha; subst a; trivial
  · exact checked8135
theorem derived8135 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8135 := by
  apply localUnsat_implies_entails f8135 [c8134, c6880, c6698, c7168, c7488, c7249] c8135 unsat8135 (by rfl) a
  have h0 : Entails.eval a c8134 := derived8134 a h
  have h1 : Entails.eval a c6880 := h 6879 (by decide)
  have h2 : Entails.eval a c6698 := h 6697 (by decide)
  have h3 : Entails.eval a c7168 := h 7167 (by decide)
  have h4 : Entails.eval a c7488 := h 7487 (by decide)
  have h5 : Entails.eval a c7249 := h 7248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8136 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨39, by decide⟩, false), (⟨48, by decide⟩, false), (⟨42, by decide⟩, false), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8136 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c548, some c546, some c3376, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8136 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8136 : lratChecker f8136 p8136 = .success := by decide +kernel
theorem unsat8136 : Unsatisfiable (PosFin 65) f8136 := by
  apply lratCheckerSound f8136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8136
  · intro a ha; simp [p8136] at ha; subst a; trivial
  · exact checked8136
theorem derived8136 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8136 := by
  apply localUnsat_implies_entails f8136 [c548, c546, c3376] c8136 unsat8136 (by rfl) a
  have h0 : Entails.eval a c548 := h 547 (by decide)
  have h1 : Entails.eval a c546 := h 545 (by decide)
  have h2 : Entails.eval a c3376 := h 3375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8137 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨33, by decide⟩, false), (⟨39, by decide⟩, false), (⟨47, by decide⟩, true), (⟨37, by decide⟩, true), (⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨42, by decide⟩, false), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8137 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c3281, some c2467, some c3385, some c2776, some c2775, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8137 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8137 : lratChecker f8137 p8137 = .success := by decide +kernel
theorem unsat8137 : Unsatisfiable (PosFin 65) f8137 := by
  apply lratCheckerSound f8137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8137
  · intro a ha; simp [p8137] at ha; subst a; trivial
  · exact checked8137
theorem derived8137 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8137 := by
  apply localUnsat_implies_entails f8137 [c7994, c3281, c2467, c3385, c2776, c2775] c8137 unsat8137 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c3281 := h 3280 (by decide)
  have h2 : Entails.eval a c2467 := h 2466 (by decide)
  have h3 : Entails.eval a c3385 := h 3384 (by decide)
  have h4 : Entails.eval a c2776 := h 2775 (by decide)
  have h5 : Entails.eval a c2775 := h 2774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8138 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8138 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8133, some c8135, some c6584, some c7300, some c6835, some c7168, some c7524, some c7349, some c7315, some c7540, some c6370, some c6629, some c8075, some c8136, some c8137, some c443, some c554, some c2000, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8138 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8138 : lratChecker f8138 p8138 = .success := by decide +kernel
theorem unsat8138 : Unsatisfiable (PosFin 65) f8138 := by
  apply lratCheckerSound f8138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8138
  · intro a ha; simp [p8138] at ha; subst a; trivial
  · exact checked8138
theorem derived8138 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8138 := by
  apply localUnsat_implies_entails f8138 [c7994, c8133, c8135, c6584, c7300, c6835, c7168, c7524, c7349, c7315, c7540, c6370, c6629, c8075, c8136, c8137, c443, c554, c2000] c8138 unsat8138 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8133 := derived8133 a h
  have h2 : Entails.eval a c8135 := derived8135 a h
  have h3 : Entails.eval a c6584 := h 6583 (by decide)
  have h4 : Entails.eval a c7300 := h 7299 (by decide)
  have h5 : Entails.eval a c6835 := h 6834 (by decide)
  have h6 : Entails.eval a c7168 := h 7167 (by decide)
  have h7 : Entails.eval a c7524 := h 7523 (by decide)
  have h8 : Entails.eval a c7349 := h 7348 (by decide)
  have h9 : Entails.eval a c7315 := h 7314 (by decide)
  have h10 : Entails.eval a c7540 := h 7539 (by decide)
  have h11 : Entails.eval a c6370 := h 6369 (by decide)
  have h12 : Entails.eval a c6629 := h 6628 (by decide)
  have h13 : Entails.eval a c8075 := derived8075 a h
  have h14 : Entails.eval a c8136 := derived8136 a h
  have h15 : Entails.eval a c8137 := derived8137 a h
  have h16 : Entails.eval a c443 := h 442 (by decide)
  have h17 : Entails.eval a c554 := h 553 (by decide)
  have h18 : Entails.eval a c2000 := h 1999 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8139 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨33, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨45, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8139 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c443, some c546, some c554, some c2000, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8139 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8139 : lratChecker f8139 p8139 = .success := by decide +kernel
theorem unsat8139 : Unsatisfiable (PosFin 65) f8139 := by
  apply lratCheckerSound f8139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8139
  · intro a ha; simp [p8139] at ha; subst a; trivial
  · exact checked8139
theorem derived8139 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8139 := by
  apply localUnsat_implies_entails f8139 [c443, c546, c554, c2000] c8139 unsat8139 (by rfl) a
  have h0 : Entails.eval a c443 := h 442 (by decide)
  have h1 : Entails.eval a c546 := h 545 (by decide)
  have h2 : Entails.eval a c554 := h 553 (by decide)
  have h3 : Entails.eval a c2000 := h 1999 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8140 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8140 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c1483, some c2000, some c1933, some c4020, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8140 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8140 : lratChecker f8140 p8140 = .success := by decide +kernel
theorem unsat8140 : Unsatisfiable (PosFin 65) f8140 := by
  apply lratCheckerSound f8140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8140
  · intro a ha; simp [p8140] at ha; subst a; trivial
  · exact checked8140
theorem derived8140 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8140 := by
  apply localUnsat_implies_entails f8140 [c8075, c1483, c2000, c1933, c4020] c8140 unsat8140 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c1483 := h 1482 (by decide)
  have h2 : Entails.eval a c2000 := h 1999 (by decide)
  have h3 : Entails.eval a c1933 := h 1932 (by decide)
  have h4 : Entails.eval a c4020 := h 4019 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8141 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8141 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c7994, some c8140, some c1265, some c444, some c4735, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8141 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8141 : lratChecker f8141 p8141 = .success := by decide +kernel
theorem unsat8141 : Unsatisfiable (PosFin 65) f8141 := by
  apply lratCheckerSound f8141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8141
  · intro a ha; simp [p8141] at ha; subst a; trivial
  · exact checked8141
theorem derived8141 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8141 := by
  apply localUnsat_implies_entails f8141 [c8075, c7994, c8140, c1265, c444, c4735] c8141 unsat8141 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8140 := derived8140 a h
  have h3 : Entails.eval a c1265 := h 1264 (by decide)
  have h4 : Entails.eval a c444 := h 443 (by decide)
  have h5 : Entails.eval a c4735 := h 4734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8142 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8142 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8133, some c7994, some c8135, some c6584, some c7300, some c6835, some c7168, some c6629, some c7524, some c7349, some c7315, some c7540, some c6370, some c8139, some c8075, some c8138, some c8141, some c3187, some c3143, some c75, some c4931, some c2350, some c89, some c10, some c5405, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8142 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked8142 : lratChecker f8142 p8142 = .success := by decide +kernel
theorem unsat8142 : Unsatisfiable (PosFin 65) f8142 := by
  apply lratCheckerSound f8142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8142
  · intro a ha; simp [p8142] at ha; subst a; trivial
  · exact checked8142
theorem derived8142 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8142 := by
  apply localUnsat_implies_entails f8142 [c8133, c7994, c8135, c6584, c7300, c6835, c7168, c6629, c7524, c7349, c7315, c7540, c6370, c8139, c8075, c8138, c8141, c3187, c3143, c75, c4931, c2350, c89, c10, c5405] c8142 unsat8142 (by rfl) a
  have h0 : Entails.eval a c8133 := derived8133 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8135 := derived8135 a h
  have h3 : Entails.eval a c6584 := h 6583 (by decide)
  have h4 : Entails.eval a c7300 := h 7299 (by decide)
  have h5 : Entails.eval a c6835 := h 6834 (by decide)
  have h6 : Entails.eval a c7168 := h 7167 (by decide)
  have h7 : Entails.eval a c6629 := h 6628 (by decide)
  have h8 : Entails.eval a c7524 := h 7523 (by decide)
  have h9 : Entails.eval a c7349 := h 7348 (by decide)
  have h10 : Entails.eval a c7315 := h 7314 (by decide)
  have h11 : Entails.eval a c7540 := h 7539 (by decide)
  have h12 : Entails.eval a c6370 := h 6369 (by decide)
  have h13 : Entails.eval a c8139 := derived8139 a h
  have h14 : Entails.eval a c8075 := derived8075 a h
  have h15 : Entails.eval a c8138 := derived8138 a h
  have h16 : Entails.eval a c8141 := derived8141 a h
  have h17 : Entails.eval a c3187 := h 3186 (by decide)
  have h18 : Entails.eval a c3143 := h 3142 (by decide)
  have h19 : Entails.eval a c75 := h 74 (by decide)
  have h20 : Entails.eval a c4931 := h 4930 (by decide)
  have h21 : Entails.eval a c2350 := h 2349 (by decide)
  have h22 : Entails.eval a c89 := h 88 (by decide)
  have h23 : Entails.eval a c10 := h 9 (by decide)
  have h24 : Entails.eval a c5405 := h 5404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8143 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8143 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8133, some c7994, some c8135, some c6584, some c7300, some c6835, some c7168, some c8142, some c6607, some c7024, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8143 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8143 : lratChecker f8143 p8143 = .success := by decide +kernel
theorem unsat8143 : Unsatisfiable (PosFin 65) f8143 := by
  apply lratCheckerSound f8143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8143
  · intro a ha; simp [p8143] at ha; subst a; trivial
  · exact checked8143
theorem derived8143 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8143 := by
  apply localUnsat_implies_entails f8143 [c8133, c7994, c8135, c6584, c7300, c6835, c7168, c8142, c6607, c7024] c8143 unsat8143 (by rfl) a
  have h0 : Entails.eval a c8133 := derived8133 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8135 := derived8135 a h
  have h3 : Entails.eval a c6584 := h 6583 (by decide)
  have h4 : Entails.eval a c7300 := h 7299 (by decide)
  have h5 : Entails.eval a c6835 := h 6834 (by decide)
  have h6 : Entails.eval a c7168 := h 7167 (by decide)
  have h7 : Entails.eval a c8142 := derived8142 a h
  have h8 : Entails.eval a c6607 := h 6606 (by decide)
  have h9 : Entails.eval a c7024 := h 7023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8144 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨45, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8144 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6403, some c6473, some c7357, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8144 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8144 : lratChecker f8144 p8144 = .success := by decide +kernel
theorem unsat8144 : Unsatisfiable (PosFin 65) f8144 := by
  apply lratCheckerSound f8144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8144
  · intro a ha; simp [p8144] at ha; subst a; trivial
  · exact checked8144
theorem derived8144 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8144 := by
  apply localUnsat_implies_entails f8144 [c6403, c6473, c7357] c8144 unsat8144 (by rfl) a
  have h0 : Entails.eval a c6403 := h 6402 (by decide)
  have h1 : Entails.eval a c6473 := h 6472 (by decide)
  have h2 : Entails.eval a c7357 := h 7356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8145 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8145 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8133, some c7994, some c8143, some c8125, some c8144, some c7168, some c7488, some c6395, some c7153, some c6370, some c7436, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8145 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8145 : lratChecker f8145 p8145 = .success := by decide +kernel
theorem unsat8145 : Unsatisfiable (PosFin 65) f8145 := by
  apply lratCheckerSound f8145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8145
  · intro a ha; simp [p8145] at ha; subst a; trivial
  · exact checked8145
theorem derived8145 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8145 := by
  apply localUnsat_implies_entails f8145 [c8133, c7994, c8143, c8125, c8144, c7168, c7488, c6395, c7153, c6370, c7436] c8145 unsat8145 (by rfl) a
  have h0 : Entails.eval a c8133 := derived8133 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8143 := derived8143 a h
  have h3 : Entails.eval a c8125 := derived8125 a h
  have h4 : Entails.eval a c8144 := derived8144 a h
  have h5 : Entails.eval a c7168 := h 7167 (by decide)
  have h6 : Entails.eval a c7488 := h 7487 (by decide)
  have h7 : Entails.eval a c6395 := h 6394 (by decide)
  have h8 : Entails.eval a c7153 := h 7152 (by decide)
  have h9 : Entails.eval a c6370 := h 6369 (by decide)
  have h10 : Entails.eval a c7436 := h 7435 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8146 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨45, by decide⟩, false), (⟨64, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8146 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8074, some c8073, some c8079, some c8084, some c6414, some c6382, some c7169, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p8146 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8146 : lratChecker f8146 p8146 = .success := by decide +kernel
theorem unsat8146 : Unsatisfiable (PosFin 65) f8146 := by
  apply lratCheckerSound f8146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8146
  · intro a ha; simp [p8146] at ha; subst a; trivial
  · exact checked8146
theorem derived8146 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8146 := by
  apply localUnsat_implies_entails f8146 [c8074, c8073, c8079, c8084, c6414, c6382, c7169] c8146 unsat8146 (by rfl) a
  have h0 : Entails.eval a c8074 := derived8074 a h
  have h1 : Entails.eval a c8073 := derived8073 a h
  have h2 : Entails.eval a c8079 := derived8079 a h
  have h3 : Entails.eval a c8084 := derived8084 a h
  have h4 : Entails.eval a c6414 := h 6413 (by decide)
  have h5 : Entails.eval a c6382 := h 6381 (by decide)
  have h6 : Entails.eval a c7169 := h 7168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8147 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8147 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7485, some c7167, some c7152, some c6863, some c6375, some c7219, some c6305, some c7302, some c7312, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8147 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8147 : lratChecker f8147 p8147 = .success := by decide +kernel
theorem unsat8147 : Unsatisfiable (PosFin 65) f8147 := by
  apply lratCheckerSound f8147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8147
  · intro a ha; simp [p8147] at ha; subst a; trivial
  · exact checked8147
theorem derived8147 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8147 := by
  apply localUnsat_implies_entails f8147 [c7485, c7167, c7152, c6863, c6375, c7219, c6305, c7302, c7312] c8147 unsat8147 (by rfl) a
  have h0 : Entails.eval a c7485 := h 7484 (by decide)
  have h1 : Entails.eval a c7167 := h 7166 (by decide)
  have h2 : Entails.eval a c7152 := h 7151 (by decide)
  have h3 : Entails.eval a c6863 := h 6862 (by decide)
  have h4 : Entails.eval a c6375 := h 6374 (by decide)
  have h5 : Entails.eval a c7219 := h 7218 (by decide)
  have h6 : Entails.eval a c6305 := h 6304 (by decide)
  have h7 : Entails.eval a c7302 := h 7301 (by decide)
  have h8 : Entails.eval a c7312 := h 7311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8148 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨58, by decide⟩, false), (⟨61, by decide⟩, false), (⟨36, by decide⟩, true), (⟨49, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8148 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6691, some c7485, some c7167, some c7152, some c7219, some c7402, some c7302, some c7328, some c6492, some c8147, some c80, some c1027, some c547, some c3371, some c4226, some c3081, some c3035, some c3186, some c2350, some c4891, some c9, some c87, some c5417, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8148 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8148 : lratChecker f8148 p8148 = .success := by decide +kernel
theorem unsat8148 : Unsatisfiable (PosFin 65) f8148 := by
  apply lratCheckerSound f8148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8148
  · intro a ha; simp [p8148] at ha; subst a; trivial
  · exact checked8148
theorem derived8148 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8148 := by
  apply localUnsat_implies_entails f8148 [c6691, c7485, c7167, c7152, c7219, c7402, c7302, c7328, c6492, c8147, c80, c1027, c547, c3371, c4226, c3081, c3035, c3186, c2350, c4891, c9, c87, c5417] c8148 unsat8148 (by rfl) a
  have h0 : Entails.eval a c6691 := h 6690 (by decide)
  have h1 : Entails.eval a c7485 := h 7484 (by decide)
  have h2 : Entails.eval a c7167 := h 7166 (by decide)
  have h3 : Entails.eval a c7152 := h 7151 (by decide)
  have h4 : Entails.eval a c7219 := h 7218 (by decide)
  have h5 : Entails.eval a c7402 := h 7401 (by decide)
  have h6 : Entails.eval a c7302 := h 7301 (by decide)
  have h7 : Entails.eval a c7328 := h 7327 (by decide)
  have h8 : Entails.eval a c6492 := h 6491 (by decide)
  have h9 : Entails.eval a c8147 := derived8147 a h
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c1027 := h 1026 (by decide)
  have h12 : Entails.eval a c547 := h 546 (by decide)
  have h13 : Entails.eval a c3371 := h 3370 (by decide)
  have h14 : Entails.eval a c4226 := h 4225 (by decide)
  have h15 : Entails.eval a c3081 := h 3080 (by decide)
  have h16 : Entails.eval a c3035 := h 3034 (by decide)
  have h17 : Entails.eval a c3186 := h 3185 (by decide)
  have h18 : Entails.eval a c2350 := h 2349 (by decide)
  have h19 : Entails.eval a c4891 := h 4890 (by decide)
  have h20 : Entails.eval a c9 := h 8 (by decide)
  have h21 : Entails.eval a c87 := h 86 (by decide)
  have h22 : Entails.eval a c5417 := h 5416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8149 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨36, by decide⟩, true), (⟨46, by decide⟩, true), (⟨38, by decide⟩, true), (⟨41, by decide⟩, true), (⟨47, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8149 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4569, some c4715, some c2671, some c2729, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p8149 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8149 : lratChecker f8149 p8149 = .success := by decide +kernel
theorem unsat8149 : Unsatisfiable (PosFin 65) f8149 := by
  apply lratCheckerSound f8149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8149
  · intro a ha; simp [p8149] at ha; subst a; trivial
  · exact checked8149
theorem derived8149 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8149 := by
  apply localUnsat_implies_entails f8149 [c4569, c4715, c2671, c2729] c8149 unsat8149 (by rfl) a
  have h0 : Entails.eval a c4569 := h 4568 (by decide)
  have h1 : Entails.eval a c4715 := h 4714 (by decide)
  have h2 : Entails.eval a c2671 := h 2670 (by decide)
  have h3 : Entails.eval a c2729 := h 2728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8150 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨49, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8150 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8133, some c8146, some c8145, some c6691, some c7485, some c7167, some c7152, some c7219, some c7402, some c7302, some c6492, some c8147, some c6773, some c7060, some c6957, some c8148, some c8149, some c725, some c1051, some c2019, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8150 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8150 : lratChecker f8150 p8150 = .success := by decide +kernel
theorem unsat8150 : Unsatisfiable (PosFin 65) f8150 := by
  apply lratCheckerSound f8150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8150
  · intro a ha; simp [p8150] at ha; subst a; trivial
  · exact checked8150
theorem derived8150 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8150 := by
  apply localUnsat_implies_entails f8150 [c8075, c8133, c8146, c8145, c6691, c7485, c7167, c7152, c7219, c7402, c7302, c6492, c8147, c6773, c7060, c6957, c8148, c8149, c725, c1051, c2019] c8150 unsat8150 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8133 := derived8133 a h
  have h2 : Entails.eval a c8146 := derived8146 a h
  have h3 : Entails.eval a c8145 := derived8145 a h
  have h4 : Entails.eval a c6691 := h 6690 (by decide)
  have h5 : Entails.eval a c7485 := h 7484 (by decide)
  have h6 : Entails.eval a c7167 := h 7166 (by decide)
  have h7 : Entails.eval a c7152 := h 7151 (by decide)
  have h8 : Entails.eval a c7219 := h 7218 (by decide)
  have h9 : Entails.eval a c7402 := h 7401 (by decide)
  have h10 : Entails.eval a c7302 := h 7301 (by decide)
  have h11 : Entails.eval a c6492 := h 6491 (by decide)
  have h12 : Entails.eval a c8147 := derived8147 a h
  have h13 : Entails.eval a c6773 := h 6772 (by decide)
  have h14 : Entails.eval a c7060 := h 7059 (by decide)
  have h15 : Entails.eval a c6957 := h 6956 (by decide)
  have h16 : Entails.eval a c8148 := derived8148 a h
  have h17 : Entails.eval a c8149 := derived8149 a h
  have h18 : Entails.eval a c725 := h 724 (by decide)
  have h19 : Entails.eval a c1051 := h 1050 (by decide)
  have h20 : Entails.eval a c2019 := h 2018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8150

end CochromaticTwenty.Certificates.FixedCore0
