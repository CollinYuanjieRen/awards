import MerLeanExperiment.Certificates.Z12Direct_4_4_0.Inputs

/-! Generated from the actual pinned z12direct_4_4_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c127 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨26, by decide⟩, false), (⟨20, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f127 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c40, some c37, some c36, some c16, some c125, some c15, some c63, some c69, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p127 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked127 : lratChecker f127 p127 = .success := by decide +kernel
theorem unsat127 : Unsatisfiable (PosFin 29) f127 := by
  apply lratCheckerSound f127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p127
  · intro a ha; simp [p127] at ha; subst a; trivial
  · exact checked127
theorem derived127 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c127 := by
  apply localUnsat_implies_entails f127 [c40, c37, c36, c16, c125, c15, c63, c69] c127 unsat127 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c128 : DefaultClause 29 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f128 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c35, some c36, some c32, some c40, some c39, some c37, some c47, some c43, some c44, some c127, some c54, some c123, some c4, some c3, some c91, some c13, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p128 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked128 : lratChecker f128 p128 = .success := by decide +kernel
theorem unsat128 : Unsatisfiable (PosFin 29) f128 := by
  apply lratCheckerSound f128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p128
  · intro a ha; simp [p128] at ha; subst a; trivial
  · exact checked128
theorem derived128 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c128 := by
  apply localUnsat_implies_entails f128 [c35, c36, c32, c40, c39, c37, c47, c43, c44, c127, c54, c123, c4, c3, c91, c13] c128 unsat128 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c127 := derived127 a h
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c129 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨22, by decide⟩, true), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f129 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c54, some c84, some c123, some c24, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p129 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked129 : lratChecker f129 p129 = .success := by decide +kernel
theorem unsat129 : Unsatisfiable (PosFin 29) f129 := by
  apply lratCheckerSound f129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p129
  · intro a ha; simp [p129] at ha; subst a; trivial
  · exact checked129
theorem derived129 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c129 := by
  apply localUnsat_implies_entails f129 [c54, c84, c123, c24] c129 unsat129 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c130 : DefaultClause 29 := directClause [(⟨16, by decide⟩, true), (⟨22, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f130 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c129, some c86, some c124, some c56, some c125, some c15, some c96, some c63, some c88, some c98, some c61, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p130 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked130 : lratChecker f130 p130 = .success := by decide +kernel
theorem unsat130 : Unsatisfiable (PosFin 29) f130 := by
  apply lratCheckerSound f130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p130
  · intro a ha; simp [p130] at ha; subst a; trivial
  · exact checked130
theorem derived130 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c130 := by
  apply localUnsat_implies_entails f130 [c129, c86, c124, c56, c125, c15, c96, c63, c88, c98, c61] c130 unsat130 (by rfl) a
  have h0 : Entails.eval a c129 := derived129 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c131 : DefaultClause 29 := directClause [(⟨22, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f131 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c128, some c36, some c129, some c124, some c86, some c12, some c56, some c130, some c11, some c123, some c85, some c105, some c82, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p131 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked131 : lratChecker f131 p131 = .success := by decide +kernel
theorem unsat131 : Unsatisfiable (PosFin 29) f131 := by
  apply lratCheckerSound f131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p131
  · intro a ha; simp [p131] at ha; subst a; trivial
  · exact checked131
theorem derived131 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c131 := by
  apply localUnsat_implies_entails f131 [c128, c36, c129, c124, c86, c12, c56, c130, c11, c123, c85, c105, c82] c131 unsat131 (by rfl) a
  have h0 : Entails.eval a c128 := derived128 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c129 := derived129 a h
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c130 := derived130 a h
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c132 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f132 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c131, some c35, some c48, some c45, some c39, some c128, some c36, some c16, some c125, some c86, some c52, some c89, some c94, some c97, some c122, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p132 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked132 : lratChecker f132 p132 = .success := by decide +kernel
theorem unsat132 : Unsatisfiable (PosFin 29) f132 := by
  apply lratCheckerSound f132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p132
  · intro a ha; simp [p132] at ha; subst a; trivial
  · exact checked132
theorem derived132 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c132 := by
  apply localUnsat_implies_entails f132 [c131, c35, c48, c45, c39, c128, c36, c16, c125, c86, c52, c89, c94, c97, c122] c132 unsat132 (by rfl) a
  have h0 : Entails.eval a c131 := derived131 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c128 := derived128 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c133 : DefaultClause 29 := directClause [(⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f133 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c128, some c35, some c36, some c131, some c48, some c39, some c45, some c132, some c54, some c84, some c4, some c24, some c111, some c99, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p133 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked133 : lratChecker f133 p133 = .success := by decide +kernel
theorem unsat133 : Unsatisfiable (PosFin 29) f133 := by
  apply lratCheckerSound f133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p133
  · intro a ha; simp [p133] at ha; subst a; trivial
  · exact checked133
theorem derived133 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c133 := by
  apply localUnsat_implies_entails f133 [c128, c35, c36, c131, c48, c39, c45, c132, c54, c84, c4, c24, c111, c99] c133 unsat133 (by rfl) a
  have h0 : Entails.eval a c128 := derived128 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c131 := derived131 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c132 := derived132 a h
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c134 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f134 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c54, some c84, some c4, some c5, some c71, some c13, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p134 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked134 : lratChecker f134 p134 = .success := by decide +kernel
theorem unsat134 : Unsatisfiable (PosFin 29) f134 := by
  apply lratCheckerSound f134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p134
  · intro a ha; simp [p134] at ha; subst a; trivial
  · exact checked134
theorem derived134 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c134 := by
  apply localUnsat_implies_entails f134 [c54, c84, c4, c5, c71, c13] c134 unsat134 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c135 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f135 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c36, some c35, some c128, some c133, some c33, some c44, some c42, some c43, some c47, some c39, some c134, some c16, some c86, some c17, some c25, some c90, some c120, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p135 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked135 : lratChecker f135 p135 = .success := by decide +kernel
theorem unsat135 : Unsatisfiable (PosFin 29) f135 := by
  apply lratCheckerSound f135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p135
  · intro a ha; simp [p135] at ha; subst a; trivial
  · exact checked135
theorem derived135 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c135 := by
  apply localUnsat_implies_entails f135 [c36, c35, c128, c133, c33, c44, c42, c43, c47, c39, c134, c16, c86, c17, c25, c90, c120] c135 unsat135 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c128 := derived128 a h
  have h3 : Entails.eval a c133 := derived133 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c134 := derived134 a h
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c136 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f136 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c135, some c36, some c86, some c109, some c53, some c22, some c107, some c65, some c66, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p136 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked136 : lratChecker f136 p136 = .success := by decide +kernel
theorem unsat136 : Unsatisfiable (PosFin 29) f136 := by
  apply lratCheckerSound f136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p136
  · intro a ha; simp [p136] at ha; subst a; trivial
  · exact checked136
theorem derived136 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c136 := by
  apply localUnsat_implies_entails f136 [c135, c36, c86, c109, c53, c22, c107, c65, c66] c136 unsat136 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c137 : DefaultClause 29 := directClause [(⟨26, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f137 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c135, some c36, some c136, some c54, some c84, some c107, some c53, some c58, some c10, some c57, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p137 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked137 : lratChecker f137 p137 = .success := by decide +kernel
theorem unsat137 : Unsatisfiable (PosFin 29) f137 := by
  apply lratCheckerSound f137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p137
  · intro a ha; simp [p137] at ha; subst a; trivial
  · exact checked137
theorem derived137 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c137 := by
  apply localUnsat_implies_entails f137 [c135, c36, c136, c54, c84, c107, c53, c58, c10, c57] c137 unsat137 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c136 := derived136 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c138 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f138 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c137, some c32, some c135, some c36, some c54, some c123, some c107, some c24, some c53, some c118, some c7, some c100, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p138 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked138 : lratChecker f138 p138 = .success := by decide +kernel
theorem unsat138 : Unsatisfiable (PosFin 29) f138 := by
  apply lratCheckerSound f138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p138
  · intro a ha; simp [p138] at ha; subst a; trivial
  · exact checked138
theorem derived138 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c138 := by
  apply localUnsat_implies_entails f138 [c137, c32, c135, c36, c54, c123, c107, c24, c53, c118, c7, c100] c138 unsat138 (by rfl) a
  have h0 : Entails.eval a c137 := derived137 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c135 := derived135 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c139 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f139 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c36, some c135, some c137, some c32, some c138, some c109, some c124, some c53, some c107, some c19, some c59, some c66, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p139 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked139 : lratChecker f139 p139 = .success := by decide +kernel
theorem unsat139 : Unsatisfiable (PosFin 29) f139 := by
  apply lratCheckerSound f139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p139
  · intro a ha; simp [p139] at ha; subst a; trivial
  · exact checked139
theorem derived139 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c139 := by
  apply localUnsat_implies_entails f139 [c36, c135, c137, c32, c138, c109, c124, c53, c107, c19, c59, c66] c139 unsat139 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c137 := derived137 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c138 := derived138 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c140 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f140 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c109, some c53, some c107, some c19, some c65, some c31, some c46, some c74, some c83, some c77, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p140 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked140 : lratChecker f140 p140 = .success := by decide +kernel
theorem unsat140 : Unsatisfiable (PosFin 29) f140 := by
  apply lratCheckerSound f140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p140
  · intro a ha; simp [p140] at ha; subst a; trivial
  · exact checked140
theorem derived140 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c140 := by
  apply localUnsat_implies_entails f140 [c139, c109, c53, c107, c19, c65, c31, c46, c74, c83, c77] c140 unsat140 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c141 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f141 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c109, some c53, some c107, some c140, some c66, some c59, some c67, some c124, some c121, some c31, some c92, some c21, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p141 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked141 : lratChecker f141 p141 = .success := by decide +kernel
theorem unsat141 : Unsatisfiable (PosFin 29) f141 := by
  apply lratCheckerSound f141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p141
  · intro a ha; simp [p141] at ha; subst a; trivial
  · exact checked141
theorem derived141 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c141 := by
  apply localUnsat_implies_entails f141 [c139, c109, c53, c107, c140, c66, c59, c67, c124, c121, c31, c92, c21] c141 unsat141 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c140 := derived140 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c142 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨21, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f142 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c141, some c54, some c107, some c53, some c64, some c100, some c60, some c7, some c8, some c31, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p142 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked142 : lratChecker f142 p142 = .success := by decide +kernel
theorem unsat142 : Unsatisfiable (PosFin 29) f142 := by
  apply lratCheckerSound f142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p142
  · intro a ha; simp [p142] at ha; subst a; trivial
  · exact checked142
theorem derived142 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c142 := by
  apply localUnsat_implies_entails f142 [c141, c54, c107, c53, c64, c100, c60, c7, c8, c31] c142 unsat142 (by rfl) a
  have h0 : Entails.eval a c141 := derived141 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c143 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f143 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c141, some c54, some c142, some c126, some c123, some c27, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p143 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked143 : lratChecker f143 p143 = .success := by decide +kernel
theorem unsat143 : Unsatisfiable (PosFin 29) f143 := by
  apply lratCheckerSound f143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p143
  · intro a ha; simp [p143] at ha; subst a; trivial
  · exact checked143
theorem derived143 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c143 := by
  apply localUnsat_implies_entails f143 [c139, c141, c54, c142, c126, c123, c27] c143 unsat143 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c141 := derived141 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c142 := derived142 a h
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c144 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f144 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c141, some c54, some c107, some c53, some c143, some c118, some c24, some c58, some c126, some c123, some c57, some c55, some c113, some c31, some c6, some c80, some c72, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p144 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked144 : lratChecker f144 p144 = .success := by decide +kernel
theorem unsat144 : Unsatisfiable (PosFin 29) f144 := by
  apply lratCheckerSound f144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p144
  · intro a ha; simp [p144] at ha; subst a; trivial
  · exact checked144
theorem derived144 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c144 := by
  apply localUnsat_implies_entails f144 [c139, c141, c54, c107, c53, c143, c118, c24, c58, c126, c123, c57, c55, c113, c31, c6, c80, c72] c144 unsat144 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c141 := derived141 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c143 := derived143 a h
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c145 : DefaultClause 29 := directClause [(⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨12, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f145 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c144, some c31, some c51, some c8, some c106, some c55, some c58, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p145 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked145 : lratChecker f145 p145 = .success := by decide +kernel
theorem unsat145 : Unsatisfiable (PosFin 29) f145 := by
  apply lratCheckerSound f145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p145
  · intro a ha; simp [p145] at ha; subst a; trivial
  · exact checked145
theorem derived145 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c145 := by
  apply localUnsat_implies_entails f145 [c139, c144, c31, c51, c8, c106, c55, c58] c145 unsat145 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c144 := derived144 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c146 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f146 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c7, some c19, some c102, some c57, some c12, some c11, some c126, some c79, some c112, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p146 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked146 : lratChecker f146 p146 = .success := by decide +kernel
theorem unsat146 : Unsatisfiable (PosFin 29) f146 := by
  apply lratCheckerSound f146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p146
  · intro a ha; simp [p146] at ha; subst a; trivial
  · exact checked146
theorem derived146 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c146 := by
  apply localUnsat_implies_entails f146 [c139, c7, c19, c102, c57, c12, c11, c126, c79, c112] c146 unsat146 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c147 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f147 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c144, some c145, some c7, some c50, some c146, some c24, some c1, some c83, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p147 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked147 : lratChecker f147 p147 = .success := by decide +kernel
theorem unsat147 : Unsatisfiable (PosFin 29) f147 := by
  apply lratCheckerSound f147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p147
  · intro a ha; simp [p147] at ha; subst a; trivial
  · exact checked147
theorem derived147 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c147 := by
  apply localUnsat_implies_entails f147 [c139, c144, c145, c7, c50, c146, c24, c1, c83] c147 unsat147 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c144 := derived144 a h
  have h2 : Entails.eval a c145 := derived145 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c146 := derived146 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c148 : DefaultClause 29 := directClause [(⟨22, by decide⟩, true), (⟨6, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f148 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c53, some c19, some c50, some c24, some c66, some c23, some c114, some c110, some c62, some c73, some c78, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p148 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked148 : lratChecker f148 p148 = .success := by decide +kernel
theorem unsat148 : Unsatisfiable (PosFin 29) f148 := by
  apply lratCheckerSound f148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p148
  · intro a ha; simp [p148] at ha; subst a; trivial
  · exact checked148
theorem derived148 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c148 := by
  apply localUnsat_implies_entails f148 [c139, c53, c19, c50, c24, c66, c23, c114, c110, c62, c73, c78] c148 unsat148 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c149 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f149 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c144, some c147, some c53, some c148, some c31, some c51, some c20, some c110, some c23, some c54, some c65, some c14, some c83, some c27, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p149 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked149 : lratChecker f149 p149 = .success := by decide +kernel
theorem unsat149 : Unsatisfiable (PosFin 29) f149 := by
  apply lratCheckerSound f149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p149
  · intro a ha; simp [p149] at ha; subst a; trivial
  · exact checked149
theorem derived149 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c149 := by
  apply localUnsat_implies_entails f149 [c139, c144, c147, c53, c148, c31, c51, c20, c110, c23, c54, c65, c14, c83, c27] c149 unsat149 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c144 := derived144 a h
  have h2 : Entails.eval a c147 := derived147 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c148 := derived148 a h
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c150 : DefaultClause 29 := directClause [(⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f150 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c53, some c149, some c144, some c31, some c51, some c20, some c18, some c110, some c52, some c29, some c81, some c117, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p150 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked150 : lratChecker f150 p150 = .success := by decide +kernel
theorem unsat150 : Unsatisfiable (PosFin 29) f150 := by
  apply lratCheckerSound f150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p150
  · intro a ha; simp [p150] at ha; subst a; trivial
  · exact checked150
theorem derived150 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c150 := by
  apply localUnsat_implies_entails f150 [c139, c53, c149, c144, c31, c51, c20, c18, c110, c52, c29, c81, c117] c150 unsat150 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c149 := derived149 a h
  have h3 : Entails.eval a c144 := derived144 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c151 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f151 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c149, some c144, some c53, some c150, some c50, some c87, some c103, some c59, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p151 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked151 : lratChecker f151 p151 = .success := by decide +kernel
theorem unsat151 : Unsatisfiable (PosFin 29) f151 := by
  apply lratCheckerSound f151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p151
  · intro a ha; simp [p151] at ha; subst a; trivial
  · exact checked151
theorem derived151 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c151 := by
  apply localUnsat_implies_entails f151 [c139, c149, c144, c53, c150, c50, c87, c103, c59] c151 unsat151 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c149 := derived149 a h
  have h2 : Entails.eval a c144 := derived144 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c150 := derived150 a h
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c152 : DefaultClause 29 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f152 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c144, some c149, some c151, some c118, some c29, some c50, some c31, some c51, some c8, some c70, some c2, some c52, some c119, some c20, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p152 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked152 : lratChecker f152 p152 = .success := by decide +kernel
theorem unsat152 : Unsatisfiable (PosFin 29) f152 := by
  apply lratCheckerSound f152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p152
  · intro a ha; simp [p152] at ha; subst a; trivial
  · exact checked152
theorem derived152 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c152 := by
  apply localUnsat_implies_entails f152 [c139, c144, c149, c151, c118, c29, c50, c31, c51, c8, c70, c2, c52, c119, c20] c152 unsat152 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c144 := derived144 a h
  have h2 : Entails.eval a c149 := derived149 a h
  have h3 : Entails.eval a c151 := derived151 a h
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c153 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f153 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c152, some c41, some c22, some c101, some c53, some c10, some c118, some c11, some c50, some c8, some c49, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p153 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked153 : lratChecker f153 p153 = .success := by decide +kernel
theorem unsat153 : Unsatisfiable (PosFin 29) f153 := by
  apply lratCheckerSound f153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p153
  · intro a ha; simp [p153] at ha; subst a; trivial
  · exact checked153
theorem derived153 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c153 := by
  apply localUnsat_implies_entails f153 [c152, c41, c22, c101, c53, c10, c118, c11, c50, c8, c49] c153 unsat153 (by rfl) a
  have h0 : Entails.eval a c152 := derived152 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c154 : DefaultClause 29 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f154 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c152, some c10, some c8, some c52, some c11, some c21, some c58, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p154 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked154 : lratChecker f154 p154 = .success := by decide +kernel
theorem unsat154 : Unsatisfiable (PosFin 29) f154 := by
  apply lratCheckerSound f154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p154
  · intro a ha; simp [p154] at ha; subst a; trivial
  · exact checked154
theorem derived154 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c154 := by
  apply localUnsat_implies_entails f154 [c139, c152, c10, c8, c52, c11, c21, c58] c154 unsat154 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c152 := derived152 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c155 : DefaultClause 29 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨5, by decide⟩, false), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f155 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c34, some c30, some c68, some c95, some c93, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p155 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked155 : lratChecker f155 p155 = .success := by decide +kernel
theorem unsat155 : Unsatisfiable (PosFin 29) f155 := by
  apply lratCheckerSound f155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p155
  · intro a ha; simp [p155] at ha; subst a; trivial
  · exact checked155
theorem derived155 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c155 := by
  apply localUnsat_implies_entails f155 [c139, c34, c30, c68, c95, c93] c155 unsat155 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c156 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f156 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c153, some c152, some c41, some c10, some c154, some c155, some c7, some c50, some c1, some c146, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p156 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked156 : lratChecker f156 p156 = .success := by decide +kernel
theorem unsat156 : Unsatisfiable (PosFin 29) f156 := by
  apply lratCheckerSound f156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p156
  · intro a ha; simp [p156] at ha; subst a; trivial
  · exact checked156
theorem derived156 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c156 := by
  apply localUnsat_implies_entails f156 [c153, c152, c41, c10, c154, c155, c7, c50, c1, c146] c156 unsat156 (by rfl) a
  have h0 : Entails.eval a c153 := derived153 a h
  have h1 : Entails.eval a c152 := derived152 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c154 := derived154 a h
  have h5 : Entails.eval a c155 := derived155 a h
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c146 := derived146 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c157 : DefaultClause 29 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f157 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c153, some c156, some c148, some c53, some c152, some c41, some c49, some c155, some c114, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p157 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked157 : lratChecker f157 p157 = .success := by decide +kernel
theorem unsat157 : Unsatisfiable (PosFin 29) f157 := by
  apply lratCheckerSound f157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p157
  · intro a ha; simp [p157] at ha; subst a; trivial
  · exact checked157
theorem derived157 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c157 := by
  apply localUnsat_implies_entails f157 [c153, c156, c148, c53, c152, c41, c49, c155, c114] c157 unsat157 (by rfl) a
  have h0 : Entails.eval a c153 := derived153 a h
  have h1 : Entails.eval a c156 := derived156 a h
  have h2 : Entails.eval a c148 := derived148 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c152 := derived152 a h
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c155 := derived155 a h
  have h8 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c158 : DefaultClause 29 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f158 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c41, some c153, some c156, some c53, some c157, some c20, some c52, some c23, some c9, some c104, some c65, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p158 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked158 : lratChecker f158 p158 = .success := by decide +kernel
theorem unsat158 : Unsatisfiable (PosFin 29) f158 := by
  apply lratCheckerSound f158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p158
  · intro a ha; simp [p158] at ha; subst a; trivial
  · exact checked158
theorem derived158 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c158 := by
  apply localUnsat_implies_entails f158 [c139, c41, c153, c156, c53, c157, c20, c52, c23, c9, c104, c65] c158 unsat158 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c153 := derived153 a h
  have h3 : Entails.eval a c156 := derived156 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c157 := derived157 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c159 : DefaultClause 29 := directClause [(⟨5, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f159 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c152, some c158, some c86, some c10, some c54, some c53, some c107, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p159 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked159 : lratChecker f159 p159 = .success := by decide +kernel
theorem unsat159 : Unsatisfiable (PosFin 29) f159 := by
  apply lratCheckerSound f159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p159
  · intro a ha; simp [p159] at ha; subst a; trivial
  · exact checked159
theorem derived159 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c159 := by
  apply localUnsat_implies_entails f159 [c152, c158, c86, c10, c54, c53, c107] c159 unsat159 (by rfl) a
  have h0 : Entails.eval a c152 := derived152 a h
  have h1 : Entails.eval a c158 := derived158 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c160 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f160 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c159, some c152, some c158, some c107, some c54, some c65, some c109, some c66, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p160 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked160 : lratChecker f160 p160 = .success := by decide +kernel
theorem unsat160 : Unsatisfiable (PosFin 29) f160 := by
  apply lratCheckerSound f160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p160
  · intro a ha; simp [p160] at ha; subst a; trivial
  · exact checked160
theorem derived160 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c160 := by
  apply localUnsat_implies_entails f160 [c159, c152, c158, c107, c54, c65, c109, c66] c160 unsat160 (by rfl) a
  have h0 : Entails.eval a c159 := derived159 a h
  have h1 : Entails.eval a c152 := derived152 a h
  have h2 : Entails.eval a c158 := derived158 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c161 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f161 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c159, some c152, some c158, some c160, some c53, some c109, some c58, some c57, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p161 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked161 : lratChecker f161 p161 = .success := by decide +kernel
theorem unsat161 : Unsatisfiable (PosFin 29) f161 := by
  apply lratCheckerSound f161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p161
  · intro a ha; simp [p161] at ha; subst a; trivial
  · exact checked161
theorem derived161 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c161 := by
  apply localUnsat_implies_entails f161 [c159, c152, c158, c160, c53, c109, c58, c57] c161 unsat161 (by rfl) a
  have h0 : Entails.eval a c159 := derived159 a h
  have h1 : Entails.eval a c152 := derived152 a h
  have h2 : Entails.eval a c158 := derived158 a h
  have h3 : Entails.eval a c160 := derived160 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c162 : DefaultClause 29 := directClause [(⟨27, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f162 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c158, some c161, some c22, some c84, some c53, some c54, some c109, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p162 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked162 : lratChecker f162 p162 = .success := by decide +kernel
theorem unsat162 : Unsatisfiable (PosFin 29) f162 := by
  apply lratCheckerSound f162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p162
  · intro a ha; simp [p162] at ha; subst a; trivial
  · exact checked162
theorem derived162 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c162 := by
  apply localUnsat_implies_entails f162 [c158, c161, c22, c84, c53, c54, c109] c162 unsat162 (by rfl) a
  have h0 : Entails.eval a c158 := derived158 a h
  have h1 : Entails.eval a c161 := derived161 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c163 : DefaultClause 29 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f163 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c152, some c162, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p163 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked163 : lratChecker f163 p163 = .success := by decide +kernel
theorem unsat163 : Unsatisfiable (PosFin 29) f163 := by
  apply lratCheckerSound f163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p163
  · intro a ha; simp [p163] at ha; subst a; trivial
  · exact checked163
theorem derived163 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c163 := by
  apply localUnsat_implies_entails f163 [c152, c162] c163 unsat163 (by rfl) a
  have h0 : Entails.eval a c152 := derived152 a h
  have h1 : Entails.eval a c162 := derived162 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c164 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f164 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c163, some c35, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p164 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked164 : lratChecker f164 p164 = .success := by decide +kernel
theorem unsat164 : Unsatisfiable (PosFin 29) f164 := by
  apply lratCheckerSound f164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p164
  · intro a ha; simp [p164] at ha; subst a; trivial
  · exact checked164
theorem derived164 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c164 := by
  apply localUnsat_implies_entails f164 [c163, c35] c164 unsat164 (by rfl) a
  have h0 : Entails.eval a c163 := derived163 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c165 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f165 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c164, some c53, some c106, some c54, some c87, some c84, some c2, some c27, some c28, some c108, some c116, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p165 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked165 : lratChecker f165 p165 = .success := by decide +kernel
theorem unsat165 : Unsatisfiable (PosFin 29) f165 := by
  apply lratCheckerSound f165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p165
  · intro a ha; simp [p165] at ha; subst a; trivial
  · exact checked165
theorem derived165 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c165 := by
  apply localUnsat_implies_entails f165 [c139, c164, c53, c106, c54, c87, c84, c2, c27, c28, c108, c116] c165 unsat165 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c164 := derived164 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c166 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f166 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c164, some c139, some c53, some c106, some c54, some c84, some c87, some c165, some c100, some c126, some c123, some c27, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p166 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked166 : lratChecker f166 p166 = .success := by decide +kernel
theorem unsat166 : Unsatisfiable (PosFin 29) f166 := by
  apply lratCheckerSound f166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p166
  · intro a ha; simp [p166] at ha; subst a; trivial
  · exact checked166
theorem derived166 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c166 := by
  apply localUnsat_implies_entails f166 [c164, c139, c53, c106, c54, c84, c87, c165, c100, c126, c123, c27] c166 unsat166 (by rfl) a
  have h0 : Entails.eval a c164 := derived164 a h
  have h1 : Entails.eval a c139 := derived139 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c165 := derived165 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c167 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f167 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c164, some c139, some c53, some c106, some c54, some c166, some c24, some c58, some c126, some c123, some c55, some c4, some c9, some c26, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p167 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked167 : lratChecker f167 p167 = .success := by decide +kernel
theorem unsat167 : Unsatisfiable (PosFin 29) f167 := by
  apply lratCheckerSound f167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p167
  · intro a ha; simp [p167] at ha; subst a; trivial
  · exact checked167
theorem derived167 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c167 := by
  apply localUnsat_implies_entails f167 [c164, c139, c53, c106, c54, c166, c24, c58, c126, c123, c55, c4, c9, c26] c167 unsat167 (by rfl) a
  have h0 : Entails.eval a c164 := derived164 a h
  have h1 : Entails.eval a c139 := derived139 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c166 := derived166 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c168 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f168 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c164, some c139, some c167, some c110, some c54, some c106, some c14, some c65, some c86, some c83, some c38, some c28, some c76, some c75, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p168 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked168 : lratChecker f168 p168 = .success := by decide +kernel
theorem unsat168 : Unsatisfiable (PosFin 29) f168 := by
  apply lratCheckerSound f168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p168
  · intro a ha; simp [p168] at ha; subst a; trivial
  · exact checked168
theorem derived168 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c168 := by
  apply localUnsat_implies_entails f168 [c164, c139, c167, c110, c54, c106, c14, c65, c86, c83, c38, c28, c76, c75] c168 unsat168 (by rfl) a
  have h0 : Entails.eval a c164 := derived164 a h
  have h1 : Entails.eval a c139 := derived139 a h
  have h2 : Entails.eval a c167 := derived167 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c169 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f169 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c164, some c139, some c167, some c110, some c54, some c106, some c168, some c66, some c18, some c59, some c67, some c124, some c121, some c92, some c28, some c16, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p169 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked169 : lratChecker f169 p169 = .success := by decide +kernel
theorem unsat169 : Unsatisfiable (PosFin 29) f169 := by
  apply lratCheckerSound f169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p169
  · intro a ha; simp [p169] at ha; subst a; trivial
  · exact checked169
theorem derived169 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c169 := by
  apply localUnsat_implies_entails f169 [c164, c139, c167, c110, c54, c106, c168, c66, c18, c59, c67, c124, c121, c92, c28, c16] c169 unsat169 (by rfl) a
  have h0 : Entails.eval a c164 := derived164 a h
  have h1 : Entails.eval a c139 := derived139 a h
  have h2 : Entails.eval a c167 := derived167 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c168 := derived168 a h
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c170 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f170 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c164, some c169, some c139, some c110, some c54, some c18, some c59, some c29, some c121, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p170 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked170 : lratChecker f170 p170 = .success := by decide +kernel
theorem unsat170 : Unsatisfiable (PosFin 29) f170 := by
  apply lratCheckerSound f170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p170
  · intro a ha; simp [p170] at ha; subst a; trivial
  · exact checked170
theorem derived170 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c170 := by
  apply localUnsat_implies_entails f170 [c164, c169, c139, c110, c54, c18, c59, c29, c121] c170 unsat170 (by rfl) a
  have h0 : Entails.eval a c164 := derived164 a h
  have h1 : Entails.eval a c169 := derived169 a h
  have h2 : Entails.eval a c139 := derived139 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c171 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f171 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c164, some c169, some c139, some c110, some c54, some c106, some c170, some c66, some c14, some c65, some c29, some c83, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p171 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked171 : lratChecker f171 p171 = .success := by decide +kernel
theorem unsat171 : Unsatisfiable (PosFin 29) f171 := by
  apply lratCheckerSound f171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p171
  · intro a ha; simp [p171] at ha; subst a; trivial
  · exact checked171
theorem derived171 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c171 := by
  apply localUnsat_implies_entails f171 [c164, c169, c139, c110, c54, c106, c170, c66, c14, c65, c29, c83] c171 unsat171 (by rfl) a
  have h0 : Entails.eval a c164 := derived164 a h
  have h1 : Entails.eval a c169 := derived169 a h
  have h2 : Entails.eval a c139 := derived139 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c170 := derived170 a h
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c172 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f172 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c171, some c53, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p172 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked172 : lratChecker f172 p172 = .success := by decide +kernel
theorem unsat172 : Unsatisfiable (PosFin 29) f172 := by
  apply lratCheckerSound f172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p172
  · intro a ha; simp [p172] at ha; subst a; trivial
  · exact checked172
theorem derived172 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c172 := by
  apply localUnsat_implies_entails f172 [c171, c53] c172 unsat172 (by rfl) a
  have h0 : Entails.eval a c171 := derived171 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c173 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f173 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c172, some c164, some c139, some c106, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p173 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked173 : lratChecker f173 p173 = .success := by decide +kernel
theorem unsat173 : Unsatisfiable (PosFin 29) f173 := by
  apply lratCheckerSound f173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p173
  · intro a ha; simp [p173] at ha; subst a; trivial
  · exact checked173
theorem derived173 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c173 := by
  apply localUnsat_implies_entails f173 [c172, c164, c139, c106] c173 unsat173 (by rfl) a
  have h0 : Entails.eval a c172 := derived172 a h
  have h1 : Entails.eval a c164 := derived164 a h
  have h2 : Entails.eval a c139 := derived139 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c174 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f174 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c173, some c54, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p174 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked174 : lratChecker f174 p174 = .success := by decide +kernel
theorem unsat174 : Unsatisfiable (PosFin 29) f174 := by
  apply lratCheckerSound f174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p174
  · intro a ha; simp [p174] at ha; subst a; trivial
  · exact checked174
theorem derived174 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c174 := by
  apply localUnsat_implies_entails f174 [c173, c54] c174 unsat174 (by rfl) a
  have h0 : Entails.eval a c173 := derived173 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c175 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f175 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c139, some c174, some c171, some c173, some c169, some c164, some c172, some c24, some c58, some c126, some c57, some c29, some c6, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p175 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked175 : lratChecker f175 p175 = .success := by decide +kernel
theorem unsat175 : Unsatisfiable (PosFin 29) f175 := by
  apply lratCheckerSound f175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p175
  · intro a ha; simp [p175] at ha; subst a; trivial
  · exact checked175
theorem derived175 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c175 := by
  apply localUnsat_implies_entails f175 [c139, c174, c171, c173, c169, c164, c172, c24, c58, c126, c57, c29, c6] c175 unsat175 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c174 := derived174 a h
  have h2 : Entails.eval a c171 := derived171 a h
  have h3 : Entails.eval a c173 := derived173 a h
  have h4 : Entails.eval a c169 := derived169 a h
  have h5 : Entails.eval a c164 := derived164 a h
  have h6 : Entails.eval a c172 := derived172 a h
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c176 : DefaultClause 29 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f176 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c175, some c172, some c164, some c115, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p176 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked176 : lratChecker f176 p176 = .success := by decide +kernel
theorem unsat176 : Unsatisfiable (PosFin 29) f176 := by
  apply lratCheckerSound f176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p176
  · intro a ha; simp [p176] at ha; subst a; trivial
  · exact checked176
theorem derived176 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c176 := by
  apply localUnsat_implies_entails f176 [c175, c172, c164, c115] c176 unsat176 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c172 := derived172 a h
  have h2 : Entails.eval a c164 := derived164 a h
  have h3 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c177 : DefaultClause 29 := directClause [(⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f177 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c175, some c174, some c139, some c87, some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p177 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked177 : lratChecker f177 p177 = .success := by decide +kernel
theorem unsat177 : Unsatisfiable (PosFin 29) f177 := by
  apply lratCheckerSound f177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p177
  · intro a ha; simp [p177] at ha; subst a; trivial
  · exact checked177
theorem derived177 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c177 := by
  apply localUnsat_implies_entails f177 [c175, c174, c139, c87] c177 unsat177 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c174 := derived174 a h
  have h2 : Entails.eval a c139 := derived139 a h
  have h3 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c178 : DefaultClause 29 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f178 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c177, some c169, some c29, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p178 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked178 : lratChecker f178 p178 = .success := by decide +kernel
theorem unsat178 : Unsatisfiable (PosFin 29) f178 := by
  apply lratCheckerSound f178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p178
  · intro a ha; simp [p178] at ha; subst a; trivial
  · exact checked178
theorem derived178 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c178 := by
  apply localUnsat_implies_entails f178 [c177, c169, c29] c178 unsat178 (by rfl) a
  have h0 : Entails.eval a c177 := derived177 a h
  have h1 : Entails.eval a c169 := derived169 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c179 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f179 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c178, some c172, some c164, some c2, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p179 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked179 : lratChecker f179 p179 = .success := by decide +kernel
theorem unsat179 : Unsatisfiable (PosFin 29) f179 := by
  apply lratCheckerSound f179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p179
  · intro a ha; simp [p179] at ha; subst a; trivial
  · exact checked179
theorem derived179 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c179 := by
  apply localUnsat_implies_entails f179 [c178, c172, c164, c2] c179 unsat179 (by rfl) a
  have h0 : Entails.eval a c178 := derived178 a h
  have h1 : Entails.eval a c172 := derived172 a h
  have h2 : Entails.eval a c164 := derived164 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c180 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f180 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c178, some c174, some c139, some c126, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p180 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked180 : lratChecker f180 p180 = .success := by decide +kernel
theorem unsat180 : Unsatisfiable (PosFin 29) f180 := by
  apply lratCheckerSound f180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p180
  · intro a ha; simp [p180] at ha; subst a; trivial
  · exact checked180
theorem derived180 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c180 := by
  apply localUnsat_implies_entails f180 [c178, c174, c139, c126] c180 unsat180 (by rfl) a
  have h0 : Entails.eval a c178 := derived178 a h
  have h1 : Entails.eval a c174 := derived174 a h
  have h2 : Entails.eval a c139 := derived139 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c181 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f181 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c179, some c180, some c177, some c176, some c100]
def p181 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked181 : lratChecker f181 p181 = .success := by decide +kernel
theorem unsat181 : Unsatisfiable (PosFin 29) f181 := by
  apply lratCheckerSound f181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p181
  · intro a ha; simp [p181] at ha; subst a; trivial
  · exact checked181
theorem derived181 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c181 := by
  apply localUnsat_implies_entails f181 [c179, c180, c177, c176, c100] c181 unsat181 (by rfl) a
  have h0 : Entails.eval a c179 := derived179 a h
  have h1 : Entails.eval a c180 := derived180 a h
  have h2 : Entails.eval a c177 := derived177 a h
  have h3 : Entails.eval a c176 := derived176 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived181

end CochromaticTwenty.Certificates.Z12Direct_4_4_0
