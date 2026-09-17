import MerLeanExperiment.Certificates.FixedCore0.Steps0500_0599

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8151 : DefaultClause 65 := directClause [(⟨1, by decide⟩, true), (⟨7, by decide⟩, true), (⟨36, by decide⟩, false), (⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨52, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8151 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1483, some c2019, some c1952, some c4019, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8151 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8151 : lratChecker f8151 p8151 = .success := by decide +kernel
theorem unsat8151 : Unsatisfiable (PosFin 65) f8151 := by
  apply lratCheckerSound f8151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8151
  · intro a ha; simp [p8151] at ha; subst a; trivial
  · exact checked8151
theorem derived8151 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8151 := by
  apply localUnsat_implies_entails f8151 [c1483, c2019, c1952, c4019] c8151 unsat8151 (by rfl) a
  have h0 : Entails.eval a c1483 := h 1482 (by decide)
  have h1 : Entails.eval a c2019 := h 2018 (by decide)
  have h2 : Entails.eval a c1952 := h 1951 (by decide)
  have h3 : Entails.eval a c4019 := h 4018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8152 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨58, by decide⟩, false), (⟨36, by decide⟩, false), (⟨49, by decide⟩, false), (⟨48, by decide⟩, false), (⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8152 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7485, some c7167, some c7152, some c7402, some c7302, some c7328, some c8151, some c724, some c445, some c2837, some c4714, some c4567, some c2728, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8152 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8152 : lratChecker f8152 p8152 = .success := by decide +kernel
theorem unsat8152 : Unsatisfiable (PosFin 65) f8152 := by
  apply lratCheckerSound f8152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8152
  · intro a ha; simp [p8152] at ha; subst a; trivial
  · exact checked8152
theorem derived8152 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8152 := by
  apply localUnsat_implies_entails f8152 [c7485, c7167, c7152, c7402, c7302, c7328, c8151, c724, c445, c2837, c4714, c4567, c2728] c8152 unsat8152 (by rfl) a
  have h0 : Entails.eval a c7485 := h 7484 (by decide)
  have h1 : Entails.eval a c7167 := h 7166 (by decide)
  have h2 : Entails.eval a c7152 := h 7151 (by decide)
  have h3 : Entails.eval a c7402 := h 7401 (by decide)
  have h4 : Entails.eval a c7302 := h 7301 (by decide)
  have h5 : Entails.eval a c7328 := h 7327 (by decide)
  have h6 : Entails.eval a c8151 := derived8151 a h
  have h7 : Entails.eval a c724 := h 723 (by decide)
  have h8 : Entails.eval a c445 := h 444 (by decide)
  have h9 : Entails.eval a c2837 := h 2836 (by decide)
  have h10 : Entails.eval a c4714 := h 4713 (by decide)
  have h11 : Entails.eval a c4567 := h 4566 (by decide)
  have h12 : Entails.eval a c2728 := h 2727 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8153 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8153 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8133, some c8146, some c8145, some c7485, some c7167, some c7152, some c7219, some c7402, some c7302, some c7328, some c8150, some c7048, some c7003, some c7101, some c8152, some c80, some c1028, some c547, some c3371, some c4215, some c3080, some c3186, some c2349, some c4931, some c9, some c87, some c5417, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8153 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked8153 : lratChecker f8153 p8153 = .success := by decide +kernel
theorem unsat8153 : Unsatisfiable (PosFin 65) f8153 := by
  apply lratCheckerSound f8153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8153
  · intro a ha; simp [p8153] at ha; subst a; trivial
  · exact checked8153
theorem derived8153 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8153 := by
  apply localUnsat_implies_entails f8153 [c8075, c8133, c8146, c8145, c7485, c7167, c7152, c7219, c7402, c7302, c7328, c8150, c7048, c7003, c7101, c8152, c80, c1028, c547, c3371, c4215, c3080, c3186, c2349, c4931, c9, c87, c5417] c8153 unsat8153 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8133 := derived8133 a h
  have h2 : Entails.eval a c8146 := derived8146 a h
  have h3 : Entails.eval a c8145 := derived8145 a h
  have h4 : Entails.eval a c7485 := h 7484 (by decide)
  have h5 : Entails.eval a c7167 := h 7166 (by decide)
  have h6 : Entails.eval a c7152 := h 7151 (by decide)
  have h7 : Entails.eval a c7219 := h 7218 (by decide)
  have h8 : Entails.eval a c7402 := h 7401 (by decide)
  have h9 : Entails.eval a c7302 := h 7301 (by decide)
  have h10 : Entails.eval a c7328 := h 7327 (by decide)
  have h11 : Entails.eval a c8150 := derived8150 a h
  have h12 : Entails.eval a c7048 := h 7047 (by decide)
  have h13 : Entails.eval a c7003 := h 7002 (by decide)
  have h14 : Entails.eval a c7101 := h 7100 (by decide)
  have h15 : Entails.eval a c8152 := derived8152 a h
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c1028 := h 1027 (by decide)
  have h18 : Entails.eval a c547 := h 546 (by decide)
  have h19 : Entails.eval a c3371 := h 3370 (by decide)
  have h20 : Entails.eval a c4215 := h 4214 (by decide)
  have h21 : Entails.eval a c3080 := h 3079 (by decide)
  have h22 : Entails.eval a c3186 := h 3185 (by decide)
  have h23 : Entails.eval a c2349 := h 2348 (by decide)
  have h24 : Entails.eval a c4931 := h 4930 (by decide)
  have h25 : Entails.eval a c9 := h 8 (by decide)
  have h26 : Entails.eval a c87 := h 86 (by decide)
  have h27 : Entails.eval a c5417 := h 5416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8154 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨40, by decide⟩, false), (⟨62, by decide⟩, true), (⟨45, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8154 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6768, some c7024, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8154 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8154 : lratChecker f8154 p8154 = .success := by decide +kernel
theorem unsat8154 : Unsatisfiable (PosFin 65) f8154 := by
  apply lratCheckerSound f8154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8154
  · intro a ha; simp [p8154] at ha; subst a; trivial
  · exact checked8154
theorem derived8154 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8154 := by
  apply localUnsat_implies_entails f8154 [c6768, c7024] c8154 unsat8154 (by rfl) a
  have h0 : Entails.eval a c6768 := h 6767 (by decide)
  have h1 : Entails.eval a c7024 := h 7023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8155 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8155 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8133, some c8146, some c8145, some c8147, some c7485, some c7167, some c7994, some c7219, some c7302, some c8154, some c7247, some c8153, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8155 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8155 : lratChecker f8155 p8155 = .success := by decide +kernel
theorem unsat8155 : Unsatisfiable (PosFin 65) f8155 := by
  apply lratCheckerSound f8155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8155
  · intro a ha; simp [p8155] at ha; subst a; trivial
  · exact checked8155
theorem derived8155 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8155 := by
  apply localUnsat_implies_entails f8155 [c8075, c8133, c8146, c8145, c8147, c7485, c7167, c7994, c7219, c7302, c8154, c7247, c8153] c8155 unsat8155 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8133 := derived8133 a h
  have h2 : Entails.eval a c8146 := derived8146 a h
  have h3 : Entails.eval a c8145 := derived8145 a h
  have h4 : Entails.eval a c8147 := derived8147 a h
  have h5 : Entails.eval a c7485 := h 7484 (by decide)
  have h6 : Entails.eval a c7167 := h 7166 (by decide)
  have h7 : Entails.eval a c7994 := derived7994 a h
  have h8 : Entails.eval a c7219 := h 7218 (by decide)
  have h9 : Entails.eval a c7302 := h 7301 (by decide)
  have h10 : Entails.eval a c8154 := derived8154 a h
  have h11 : Entails.eval a c7247 := h 7246 (by decide)
  have h12 : Entails.eval a c8153 := derived8153 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8156 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨44, by decide⟩, true), (⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8156 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7360, some c7537, some c7312, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8156 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8156 : lratChecker f8156 p8156 = .success := by decide +kernel
theorem unsat8156 : Unsatisfiable (PosFin 65) f8156 := by
  apply lratCheckerSound f8156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8156
  · intro a ha; simp [p8156] at ha; subst a; trivial
  · exact checked8156
theorem derived8156 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8156 := by
  apply localUnsat_implies_entails f8156 [c7360, c7537, c7312] c8156 unsat8156 (by rfl) a
  have h0 : Entails.eval a c7360 := h 7359 (by decide)
  have h1 : Entails.eval a c7537 := h 7536 (by decide)
  have h2 : Entails.eval a c7312 := h 7311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8157 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8157 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8133, some c8146, some c8145, some c8075, some c7167, some c7485, some c8156, some c6375, some c8155, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8157 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8157 : lratChecker f8157 p8157 = .success := by decide +kernel
theorem unsat8157 : Unsatisfiable (PosFin 65) f8157 := by
  apply lratCheckerSound f8157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8157
  · intro a ha; simp [p8157] at ha; subst a; trivial
  · exact checked8157
theorem derived8157 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8157 := by
  apply localUnsat_implies_entails f8157 [c8133, c8146, c8145, c8075, c7167, c7485, c8156, c6375, c8155] c8157 unsat8157 (by rfl) a
  have h0 : Entails.eval a c8133 := derived8133 a h
  have h1 : Entails.eval a c8146 := derived8146 a h
  have h2 : Entails.eval a c8145 := derived8145 a h
  have h3 : Entails.eval a c8075 := derived8075 a h
  have h4 : Entails.eval a c7167 := h 7166 (by decide)
  have h5 : Entails.eval a c7485 := h 7484 (by decide)
  have h6 : Entails.eval a c8156 := derived8156 a h
  have h7 : Entails.eval a c6375 := h 6374 (by decide)
  have h8 : Entails.eval a c8155 := derived8155 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8158 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨52, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8158 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7478, some c7451, some c6492, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8158 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8158 : lratChecker f8158 p8158 = .success := by decide +kernel
theorem unsat8158 : Unsatisfiable (PosFin 65) f8158 := by
  apply lratCheckerSound f8158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8158
  · intro a ha; simp [p8158] at ha; subst a; trivial
  · exact checked8158
theorem derived8158 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8158 := by
  apply localUnsat_implies_entails f8158 [c7478, c7451, c6492] c8158 unsat8158 (by rfl) a
  have h0 : Entails.eval a c7478 := h 7477 (by decide)
  have h1 : Entails.eval a c7451 := h 7450 (by decide)
  have h2 : Entails.eval a c6492 := h 6491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8159 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8159 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7548, some c8156, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8159 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8159 : lratChecker f8159 p8159 = .success := by decide +kernel
theorem unsat8159 : Unsatisfiable (PosFin 65) f8159 := by
  apply lratCheckerSound f8159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8159
  · intro a ha; simp [p8159] at ha; subst a; trivial
  · exact checked8159
theorem derived8159 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8159 := by
  apply localUnsat_implies_entails f8159 [c7548, c8156] c8159 unsat8159 (by rfl) a
  have h0 : Entails.eval a c7548 := h 7547 (by decide)
  have h1 : Entails.eval a c8156 := derived8156 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8160 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8160 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8133, some c8146, some c8145, some c8157, some c8159, some c6479, some c8158, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8160 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8160 : lratChecker f8160 p8160 = .success := by decide +kernel
theorem unsat8160 : Unsatisfiable (PosFin 65) f8160 := by
  apply lratCheckerSound f8160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8160
  · intro a ha; simp [p8160] at ha; subst a; trivial
  · exact checked8160
theorem derived8160 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8160 := by
  apply localUnsat_implies_entails f8160 [c8075, c8133, c8146, c8145, c8157, c8159, c6479, c8158] c8160 unsat8160 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8133 := derived8133 a h
  have h2 : Entails.eval a c8146 := derived8146 a h
  have h3 : Entails.eval a c8145 := derived8145 a h
  have h4 : Entails.eval a c8157 := derived8157 a h
  have h5 : Entails.eval a c8159 := derived8159 a h
  have h6 : Entails.eval a c6479 := h 6478 (by decide)
  have h7 : Entails.eval a c8158 := derived8158 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8161 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8161 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7472, some c7445, some c6485, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8161 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8161 : lratChecker f8161 p8161 = .success := by decide +kernel
theorem unsat8161 : Unsatisfiable (PosFin 65) f8161 := by
  apply lratCheckerSound f8161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8161
  · intro a ha; simp [p8161] at ha; subst a; trivial
  · exact checked8161
theorem derived8161 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8161 := by
  apply localUnsat_implies_entails f8161 [c7472, c7445, c6485] c8161 unsat8161 (by rfl) a
  have h0 : Entails.eval a c7472 := h 7471 (by decide)
  have h1 : Entails.eval a c7445 := h 7444 (by decide)
  have h2 : Entails.eval a c6485 := h 6484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8162 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨62, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8162 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6484, some c6490, some c6489, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8162 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8162 : lratChecker f8162 p8162 = .success := by decide +kernel
theorem unsat8162 : Unsatisfiable (PosFin 65) f8162 := by
  apply lratCheckerSound f8162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8162
  · intro a ha; simp [p8162] at ha; subst a; trivial
  · exact checked8162
theorem derived8162 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8162 := by
  apply localUnsat_implies_entails f8162 [c6484, c6490, c6489] c8162 unsat8162 (by rfl) a
  have h0 : Entails.eval a c6484 := h 6483 (by decide)
  have h1 : Entails.eval a c6490 := h 6489 (by decide)
  have h2 : Entails.eval a c6489 := h 6488 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8163 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨62, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨40, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8163 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7446, some c7444, some c7448, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8163 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8163 : lratChecker f8163 p8163 = .success := by decide +kernel
theorem unsat8163 : Unsatisfiable (PosFin 65) f8163 := by
  apply lratCheckerSound f8163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8163
  · intro a ha; simp [p8163] at ha; subst a; trivial
  · exact checked8163
theorem derived8163 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8163 := by
  apply localUnsat_implies_entails f8163 [c7446, c7444, c7448] c8163 unsat8163 (by rfl) a
  have h0 : Entails.eval a c7446 := h 7445 (by decide)
  have h1 : Entails.eval a c7444 := h 7443 (by decide)
  have h2 : Entails.eval a c7448 := h 7447 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8164 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8164 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8160, some c8075, some c7994, some c8158, some c8161, some c8163, some c8162, some c7481, some c7464, some c6896, some c6307, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8164 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8164 : lratChecker f8164 p8164 = .success := by decide +kernel
theorem unsat8164 : Unsatisfiable (PosFin 65) f8164 := by
  apply lratCheckerSound f8164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8164
  · intro a ha; simp [p8164] at ha; subst a; trivial
  · exact checked8164
theorem derived8164 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8164 := by
  apply localUnsat_implies_entails f8164 [c8160, c8075, c7994, c8158, c8161, c8163, c8162, c7481, c7464, c6896, c6307] c8164 unsat8164 (by rfl) a
  have h0 : Entails.eval a c8160 := derived8160 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8158 := derived8158 a h
  have h4 : Entails.eval a c8161 := derived8161 a h
  have h5 : Entails.eval a c8163 := derived8163 a h
  have h6 : Entails.eval a c8162 := derived8162 a h
  have h7 : Entails.eval a c7481 := h 7480 (by decide)
  have h8 : Entails.eval a c7464 := h 7463 (by decide)
  have h9 : Entails.eval a c6896 := h 6895 (by decide)
  have h10 : Entails.eval a c6307 := h 6306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8165 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨42, by decide⟩, true), (⟨62, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8165 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7456, some c7466, some c7464, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8165 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8165 : lratChecker f8165 p8165 = .success := by decide +kernel
theorem unsat8165 : Unsatisfiable (PosFin 65) f8165 := by
  apply lratCheckerSound f8165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8165
  · intro a ha; simp [p8165] at ha; subst a; trivial
  · exact checked8165
theorem derived8165 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8165 := by
  apply localUnsat_implies_entails f8165 [c7456, c7466, c7464] c8165 unsat8165 (by rfl) a
  have h0 : Entails.eval a c7456 := h 7455 (by decide)
  have h1 : Entails.eval a c7466 := h 7465 (by decide)
  have h2 : Entails.eval a c7464 := h 7463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8166 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8166 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6896, some c6307, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8166 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8166 : lratChecker f8166 p8166 = .success := by decide +kernel
theorem unsat8166 : Unsatisfiable (PosFin 65) f8166 := by
  apply lratCheckerSound f8166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8166
  · intro a ha; simp [p8166] at ha; subst a; trivial
  · exact checked8166
theorem derived8166 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8166 := by
  apply localUnsat_implies_entails f8166 [c6896, c6307] c8166 unsat8166 (by rfl) a
  have h0 : Entails.eval a c6896 := h 6895 (by decide)
  have h1 : Entails.eval a c6307 := h 6306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8167 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨62, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8167 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8160, some c8075, some c7994, some c8165, some c8166, some c6900, some c6313, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8167 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8167 : lratChecker f8167 p8167 = .success := by decide +kernel
theorem unsat8167 : Unsatisfiable (PosFin 65) f8167 := by
  apply lratCheckerSound f8167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8167
  · intro a ha; simp [p8167] at ha; subst a; trivial
  · exact checked8167
theorem derived8167 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8167 := by
  apply localUnsat_implies_entails f8167 [c8160, c8075, c7994, c8165, c8166, c6900, c6313] c8167 unsat8167 (by rfl) a
  have h0 : Entails.eval a c8160 := derived8160 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8165 := derived8165 a h
  have h4 : Entails.eval a c8166 := derived8166 a h
  have h5 : Entails.eval a c6900 := h 6899 (by decide)
  have h6 : Entails.eval a c6313 := h 6312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8168 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨62, by decide⟩, false), (⟨47, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8168 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6341, some c6313, some c6839, some c6668, some c6570, some c6792, some c6791, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8168 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8168 : lratChecker f8168 p8168 = .success := by decide +kernel
theorem unsat8168 : Unsatisfiable (PosFin 65) f8168 := by
  apply lratCheckerSound f8168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8168
  · intro a ha; simp [p8168] at ha; subst a; trivial
  · exact checked8168
theorem derived8168 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8168 := by
  apply localUnsat_implies_entails f8168 [c7994, c6341, c6313, c6839, c6668, c6570, c6792, c6791] c8168 unsat8168 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6341 := h 6340 (by decide)
  have h2 : Entails.eval a c6313 := h 6312 (by decide)
  have h3 : Entails.eval a c6839 := h 6838 (by decide)
  have h4 : Entails.eval a c6668 := h 6667 (by decide)
  have h5 : Entails.eval a c6570 := h 6569 (by decide)
  have h6 : Entails.eval a c6792 := h 6791 (by decide)
  have h7 : Entails.eval a c6791 := h 6790 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8169 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8169 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6873, some c6875, some c6882, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8169 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8169 : lratChecker f8169 p8169 = .success := by decide +kernel
theorem unsat8169 : Unsatisfiable (PosFin 65) f8169 := by
  apply lratCheckerSound f8169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8169
  · intro a ha; simp [p8169] at ha; subst a; trivial
  · exact checked8169
theorem derived8169 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8169 := by
  apply localUnsat_implies_entails f8169 [c6873, c6875, c6882] c8169 unsat8169 (by rfl) a
  have h0 : Entails.eval a c6873 := h 6872 (by decide)
  have h1 : Entails.eval a c6875 := h 6874 (by decide)
  have h2 : Entails.eval a c6882 := h 6881 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8170 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨62, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8170 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8168, some c6307, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8170 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8170 : lratChecker f8170 p8170 = .success := by decide +kernel
theorem unsat8170 : Unsatisfiable (PosFin 65) f8170 := by
  apply lratCheckerSound f8170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8170
  · intro a ha; simp [p8170] at ha; subst a; trivial
  · exact checked8170
theorem derived8170 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8170 := by
  apply localUnsat_implies_entails f8170 [c7994, c8168, c6307] c8170 unsat8170 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8168 := derived8168 a h
  have h2 : Entails.eval a c6307 := h 6306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8171 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8171 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7375, some c7288, some c7266, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8171 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8171 : lratChecker f8171 p8171 = .success := by decide +kernel
theorem unsat8171 : Unsatisfiable (PosFin 65) f8171 := by
  apply lratCheckerSound f8171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8171
  · intro a ha; simp [p8171] at ha; subst a; trivial
  · exact checked8171
theorem derived8171 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8171 := by
  apply localUnsat_implies_entails f8171 [c7375, c7288, c7266] c8171 unsat8171 (by rfl) a
  have h0 : Entails.eval a c7375 := h 7374 (by decide)
  have h1 : Entails.eval a c7288 := h 7287 (by decide)
  have h2 : Entails.eval a c7266 := h 7265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8172 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8172 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8164, some c8160, some c8075, some c7994, some c8167, some c8162, some c8169, some c8170, some c8171, some c7378, some c6868, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8172 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8172 : lratChecker f8172 p8172 = .success := by decide +kernel
theorem unsat8172 : Unsatisfiable (PosFin 65) f8172 := by
  apply lratCheckerSound f8172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8172
  · intro a ha; simp [p8172] at ha; subst a; trivial
  · exact checked8172
theorem derived8172 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8172 := by
  apply localUnsat_implies_entails f8172 [c8164, c8160, c8075, c7994, c8167, c8162, c8169, c8170, c8171, c7378, c6868] c8172 unsat8172 (by rfl) a
  have h0 : Entails.eval a c8164 := derived8164 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8167 := derived8167 a h
  have h5 : Entails.eval a c8162 := derived8162 a h
  have h6 : Entails.eval a c8169 := derived8169 a h
  have h7 : Entails.eval a c8170 := derived8170 a h
  have h8 : Entails.eval a c8171 := derived8171 a h
  have h9 : Entails.eval a c7378 := h 7377 (by decide)
  have h10 : Entails.eval a c6868 := h 6867 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8173 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8173 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7284, some c7376, some c7465, some c7262, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8173 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8173 : lratChecker f8173 p8173 = .success := by decide +kernel
theorem unsat8173 : Unsatisfiable (PosFin 65) f8173 := by
  apply lratCheckerSound f8173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8173
  · intro a ha; simp [p8173] at ha; subst a; trivial
  · exact checked8173
theorem derived8173 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8173 := by
  apply localUnsat_implies_entails f8173 [c7284, c7376, c7465, c7262] c8173 unsat8173 (by rfl) a
  have h0 : Entails.eval a c7284 := h 7283 (by decide)
  have h1 : Entails.eval a c7376 := h 7375 (by decide)
  have h2 : Entails.eval a c7465 := h 7464 (by decide)
  have h3 : Entails.eval a c7262 := h 7261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8174 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8174 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8164, some c7994, some c8172, some c8173, some c6308, some c6496, some c7535, some c6904, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8174 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8174 : lratChecker f8174 p8174 = .success := by decide +kernel
theorem unsat8174 : Unsatisfiable (PosFin 65) f8174 := by
  apply lratCheckerSound f8174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8174
  · intro a ha; simp [p8174] at ha; subst a; trivial
  · exact checked8174
theorem derived8174 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8174 := by
  apply localUnsat_implies_entails f8174 [c8164, c7994, c8172, c8173, c6308, c6496, c7535, c6904] c8174 unsat8174 (by rfl) a
  have h0 : Entails.eval a c8164 := derived8164 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8172 := derived8172 a h
  have h3 : Entails.eval a c8173 := derived8173 a h
  have h4 : Entails.eval a c6308 := h 6307 (by decide)
  have h5 : Entails.eval a c6496 := h 6495 (by decide)
  have h6 : Entails.eval a c7535 := h 7534 (by decide)
  have h7 : Entails.eval a c6904 := h 6903 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8175 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8175 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6897, some c6879, some c6492, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8175 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8175 : lratChecker f8175 p8175 = .success := by decide +kernel
theorem unsat8175 : Unsatisfiable (PosFin 65) f8175 := by
  apply lratCheckerSound f8175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8175
  · intro a ha; simp [p8175] at ha; subst a; trivial
  · exact checked8175
theorem derived8175 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8175 := by
  apply localUnsat_implies_entails f8175 [c6897, c6879, c6492] c8175 unsat8175 (by rfl) a
  have h0 : Entails.eval a c6897 := h 6896 (by decide)
  have h1 : Entails.eval a c6879 := h 6878 (by decide)
  have h2 : Entails.eval a c6492 := h 6491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8176 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨62, by decide⟩, true), (⟨35, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8176 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c6321, some c6863, some c7386, some c7994, some c6932, some c6306, some c6934, some c6500, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8176 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8176 : lratChecker f8176 p8176 = .success := by decide +kernel
theorem unsat8176 : Unsatisfiable (PosFin 65) f8176 := by
  apply lratCheckerSound f8176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8176
  · intro a ha; simp [p8176] at ha; subst a; trivial
  · exact checked8176
theorem derived8176 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8176 := by
  apply localUnsat_implies_entails f8176 [c8075, c6321, c6863, c7386, c7994, c6932, c6306, c6934, c6500] c8176 unsat8176 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c6321 := h 6320 (by decide)
  have h2 : Entails.eval a c6863 := h 6862 (by decide)
  have h3 : Entails.eval a c7386 := h 7385 (by decide)
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c6932 := h 6931 (by decide)
  have h6 : Entails.eval a c6306 := h 6305 (by decide)
  have h7 : Entails.eval a c6934 := h 6933 (by decide)
  have h8 : Entails.eval a c6500 := h 6499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8177 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨35, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8177 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c6321, some c6863, some c7386, some c6278, some c7994, some c8176, some c7937, some c7412, some c7419, some c6672, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8177 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8177 : lratChecker f8177 p8177 = .success := by decide +kernel
theorem unsat8177 : Unsatisfiable (PosFin 65) f8177 := by
  apply lratCheckerSound f8177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8177
  · intro a ha; simp [p8177] at ha; subst a; trivial
  · exact checked8177
theorem derived8177 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8177 := by
  apply localUnsat_implies_entails f8177 [c8075, c6321, c6863, c7386, c6278, c7994, c8176, c7937, c7412, c7419, c6672] c8177 unsat8177 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c6321 := h 6320 (by decide)
  have h2 : Entails.eval a c6863 := h 6862 (by decide)
  have h3 : Entails.eval a c7386 := h 7385 (by decide)
  have h4 : Entails.eval a c6278 := h 6277 (by decide)
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c8176 := derived8176 a h
  have h7 : Entails.eval a c7937 := derived7937 a h
  have h8 : Entails.eval a c7412 := h 7411 (by decide)
  have h9 : Entails.eval a c7419 := h 7418 (by decide)
  have h10 : Entails.eval a c6672 := h 6671 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8178 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8178 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8164, some c8174, some c8075, some c8175, some c8177, some c6321, some c6863, some c7386, some c6492, some c7152, some c7203, some c7125, some c8160, some c7470, some c7422, some c7323, some c7286, some c7415, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8178 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8178 : lratChecker f8178 p8178 = .success := by decide +kernel
theorem unsat8178 : Unsatisfiable (PosFin 65) f8178 := by
  apply lratCheckerSound f8178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8178
  · intro a ha; simp [p8178] at ha; subst a; trivial
  · exact checked8178
theorem derived8178 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8178 := by
  apply localUnsat_implies_entails f8178 [c8164, c8174, c8075, c8175, c8177, c6321, c6863, c7386, c6492, c7152, c7203, c7125, c8160, c7470, c7422, c7323, c7286, c7415] c8178 unsat8178 (by rfl) a
  have h0 : Entails.eval a c8164 := derived8164 a h
  have h1 : Entails.eval a c8174 := derived8174 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c8175 := derived8175 a h
  have h4 : Entails.eval a c8177 := derived8177 a h
  have h5 : Entails.eval a c6321 := h 6320 (by decide)
  have h6 : Entails.eval a c6863 := h 6862 (by decide)
  have h7 : Entails.eval a c7386 := h 7385 (by decide)
  have h8 : Entails.eval a c6492 := h 6491 (by decide)
  have h9 : Entails.eval a c7152 := h 7151 (by decide)
  have h10 : Entails.eval a c7203 := h 7202 (by decide)
  have h11 : Entails.eval a c7125 := h 7124 (by decide)
  have h12 : Entails.eval a c8160 := derived8160 a h
  have h13 : Entails.eval a c7470 := h 7469 (by decide)
  have h14 : Entails.eval a c7422 := h 7421 (by decide)
  have h15 : Entails.eval a c7323 := h 7322 (by decide)
  have h16 : Entails.eval a c7286 := h 7285 (by decide)
  have h17 : Entails.eval a c7415 := h 7414 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8179 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8179 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c7994, some c8164, some c8174, some c8175, some c6863, some c6321, some c7152, some c7386, some c6278, some c8177, some c6676, some c8178, some c6313, some c6312, some c7246, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8179 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8179 : lratChecker f8179 p8179 = .success := by decide +kernel
theorem unsat8179 : Unsatisfiable (PosFin 65) f8179 := by
  apply lratCheckerSound f8179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8179
  · intro a ha; simp [p8179] at ha; subst a; trivial
  · exact checked8179
theorem derived8179 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8179 := by
  apply localUnsat_implies_entails f8179 [c8075, c7994, c8164, c8174, c8175, c6863, c6321, c7152, c7386, c6278, c8177, c6676, c8178, c6313, c6312, c7246] c8179 unsat8179 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8164 := derived8164 a h
  have h3 : Entails.eval a c8174 := derived8174 a h
  have h4 : Entails.eval a c8175 := derived8175 a h
  have h5 : Entails.eval a c6863 := h 6862 (by decide)
  have h6 : Entails.eval a c6321 := h 6320 (by decide)
  have h7 : Entails.eval a c7152 := h 7151 (by decide)
  have h8 : Entails.eval a c7386 := h 7385 (by decide)
  have h9 : Entails.eval a c6278 := h 6277 (by decide)
  have h10 : Entails.eval a c8177 := derived8177 a h
  have h11 : Entails.eval a c6676 := h 6675 (by decide)
  have h12 : Entails.eval a c8178 := derived8178 a h
  have h13 : Entails.eval a c6313 := h 6312 (by decide)
  have h14 : Entails.eval a c6312 := h 6311 (by decide)
  have h15 : Entails.eval a c7246 := h 7245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8180 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨62, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8180 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6452, some c6451, some c6455, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8180 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8180 : lratChecker f8180 p8180 = .success := by decide +kernel
theorem unsat8180 : Unsatisfiable (PosFin 65) f8180 := by
  apply lratCheckerSound f8180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8180
  · intro a ha; simp [p8180] at ha; subst a; trivial
  · exact checked8180
theorem derived8180 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8180 := by
  apply localUnsat_implies_entails f8180 [c7994, c6452, c6451, c6455] c8180 unsat8180 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6452 := h 6451 (by decide)
  have h2 : Entails.eval a c6451 := h 6450 (by decide)
  have h3 : Entails.eval a c6455 := h 6454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8181 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨62, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8181 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8180, some c6417, some c6483, some c7282, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8181 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8181 : lratChecker f8181 p8181 = .success := by decide +kernel
theorem unsat8181 : Unsatisfiable (PosFin 65) f8181 := by
  apply lratCheckerSound f8181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8181
  · intro a ha; simp [p8181] at ha; subst a; trivial
  · exact checked8181
theorem derived8181 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8181 := by
  apply localUnsat_implies_entails f8181 [c8180, c6417, c6483, c7282] c8181 unsat8181 (by rfl) a
  have h0 : Entails.eval a c8180 := derived8180 a h
  have h1 : Entails.eval a c6417 := h 6416 (by decide)
  have h2 : Entails.eval a c6483 := h 6482 (by decide)
  have h3 : Entails.eval a c7282 := h 7281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8182 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨57, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8182 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6935, some c7538, some c7544, some c6955, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8182 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8182 : lratChecker f8182 p8182 = .success := by decide +kernel
theorem unsat8182 : Unsatisfiable (PosFin 65) f8182 := by
  apply lratCheckerSound f8182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8182
  · intro a ha; simp [p8182] at ha; subst a; trivial
  · exact checked8182
theorem derived8182 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8182 := by
  apply localUnsat_implies_entails f8182 [c6935, c7538, c7544, c6955] c8182 unsat8182 (by rfl) a
  have h0 : Entails.eval a c6935 := h 6934 (by decide)
  have h1 : Entails.eval a c7538 := h 7537 (by decide)
  have h2 : Entails.eval a c7544 := h 7543 (by decide)
  have h3 : Entails.eval a c6955 := h 6954 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8183 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8183 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6474, some c6476, some c6480, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8183 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8183 : lratChecker f8183 p8183 = .success := by decide +kernel
theorem unsat8183 : Unsatisfiable (PosFin 65) f8183 := by
  apply lratCheckerSound f8183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8183
  · intro a ha; simp [p8183] at ha; subst a; trivial
  · exact checked8183
theorem derived8183 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8183 := by
  apply localUnsat_implies_entails f8183 [c6474, c6476, c6480] c8183 unsat8183 (by rfl) a
  have h0 : Entails.eval a c6474 := h 6473 (by decide)
  have h1 : Entails.eval a c6476 := h 6475 (by decide)
  have h2 : Entails.eval a c6480 := h 6479 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8184 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨62, by decide⟩, false), (⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8184 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8181, some c8180, some c7994, some c7281, some c6867, some c6411, some c6833, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8184 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8184 : lratChecker f8184 p8184 = .success := by decide +kernel
theorem unsat8184 : Unsatisfiable (PosFin 65) f8184 := by
  apply lratCheckerSound f8184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8184
  · intro a ha; simp [p8184] at ha; subst a; trivial
  · exact checked8184
theorem derived8184 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8184 := by
  apply localUnsat_implies_entails f8184 [c8181, c8180, c7994, c7281, c6867, c6411, c6833] c8184 unsat8184 (by rfl) a
  have h0 : Entails.eval a c8181 := derived8181 a h
  have h1 : Entails.eval a c8180 := derived8180 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c7281 := h 7280 (by decide)
  have h4 : Entails.eval a c6867 := h 6866 (by decide)
  have h5 : Entails.eval a c6411 := h 6410 (by decide)
  have h6 : Entails.eval a c6833 := h 6832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8185 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8185 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8160, some c8182, some c8075, some c7994, some c7280, some c7266, some c6660, some c6718, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8185 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8185 : lratChecker f8185 p8185 = .success := by decide +kernel
theorem unsat8185 : Unsatisfiable (PosFin 65) f8185 := by
  apply lratCheckerSound f8185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8185
  · intro a ha; simp [p8185] at ha; subst a; trivial
  · exact checked8185
theorem derived8185 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8185 := by
  apply localUnsat_implies_entails f8185 [c8160, c8182, c8075, c7994, c7280, c7266, c6660, c6718] c8185 unsat8185 (by rfl) a
  have h0 : Entails.eval a c8160 := derived8160 a h
  have h1 : Entails.eval a c8182 := derived8182 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c7280 := h 7279 (by decide)
  have h5 : Entails.eval a c7266 := h 7265 (by decide)
  have h6 : Entails.eval a c6660 := h 6659 (by decide)
  have h7 : Entails.eval a c6718 := h 6717 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8186 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8186 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8160, some c8179, some c8183, some c7994, some c8180, some c8181, some c8184, some c8185, some c6411, some c6409, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8186 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8186 : lratChecker f8186 p8186 = .success := by decide +kernel
theorem unsat8186 : Unsatisfiable (PosFin 65) f8186 := by
  apply lratCheckerSound f8186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8186
  · intro a ha; simp [p8186] at ha; subst a; trivial
  · exact checked8186
theorem derived8186 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8186 := by
  apply localUnsat_implies_entails f8186 [c8075, c8160, c8179, c8183, c7994, c8180, c8181, c8184, c8185, c6411, c6409] c8186 unsat8186 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8179 := derived8179 a h
  have h3 : Entails.eval a c8183 := derived8183 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c8180 := derived8180 a h
  have h6 : Entails.eval a c8181 := derived8181 a h
  have h7 : Entails.eval a c8184 := derived8184 a h
  have h8 : Entails.eval a c8185 := derived8185 a h
  have h9 : Entails.eval a c6411 := h 6410 (by decide)
  have h10 : Entails.eval a c6409 := h 6408 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8187 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨62, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8187 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6411, some c6412, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8187 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8187 : lratChecker f8187 p8187 = .success := by decide +kernel
theorem unsat8187 : Unsatisfiable (PosFin 65) f8187 := by
  apply lratCheckerSound f8187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8187
  · intro a ha; simp [p8187] at ha; subst a; trivial
  · exact checked8187
theorem derived8187 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8187 := by
  apply localUnsat_implies_entails f8187 [c7994, c6411, c6412] c8187 unsat8187 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6411 := h 6410 (by decide)
  have h2 : Entails.eval a c6412 := h 6411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8188 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨62, by decide⟩, true), (⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8188 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6453, some c7274, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8188 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8188 : lratChecker f8188 p8188 = .success := by decide +kernel
theorem unsat8188 : Unsatisfiable (PosFin 65) f8188 := by
  apply lratCheckerSound f8188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8188
  · intro a ha; simp [p8188] at ha; subst a; trivial
  · exact checked8188
theorem derived8188 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8188 := by
  apply localUnsat_implies_entails f8188 [c6453, c7274] c8188 unsat8188 (by rfl) a
  have h0 : Entails.eval a c6453 := h 6452 (by decide)
  have h1 : Entails.eval a c7274 := h 7273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8189 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8189 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8160, some c8075, some c7994, some c8179, some c8183, some c8186, some c8187, some c8188, some c6452, some c7280, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8189 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8189 : lratChecker f8189 p8189 = .success := by decide +kernel
theorem unsat8189 : Unsatisfiable (PosFin 65) f8189 := by
  apply lratCheckerSound f8189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8189
  · intro a ha; simp [p8189] at ha; subst a; trivial
  · exact checked8189
theorem derived8189 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8189 := by
  apply localUnsat_implies_entails f8189 [c8160, c8075, c7994, c8179, c8183, c8186, c8187, c8188, c6452, c7280] c8189 unsat8189 (by rfl) a
  have h0 : Entails.eval a c8160 := derived8160 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8179 := derived8179 a h
  have h4 : Entails.eval a c8183 := derived8183 a h
  have h5 : Entails.eval a c8186 := derived8186 a h
  have h6 : Entails.eval a c8187 := derived8187 a h
  have h7 : Entails.eval a c8188 := derived8188 a h
  have h8 : Entails.eval a c6452 := h 6451 (by decide)
  have h9 : Entails.eval a c7280 := h 7279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8190 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨52, by decide⟩, false), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8190 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7280, some c7360, some c6467, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8190 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8190 : lratChecker f8190 p8190 = .success := by decide +kernel
theorem unsat8190 : Unsatisfiable (PosFin 65) f8190 := by
  apply lratCheckerSound f8190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8190
  · intro a ha; simp [p8190] at ha; subst a; trivial
  · exact checked8190
theorem derived8190 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8190 := by
  apply localUnsat_implies_entails f8190 [c7280, c7360, c6467] c8190 unsat8190 (by rfl) a
  have h0 : Entails.eval a c7280 := h 7279 (by decide)
  have h1 : Entails.eval a c7360 := h 7359 (by decide)
  have h2 : Entails.eval a c6467 := h 6466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8191 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8191 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8075, some c8190, some c6550, some c6376, some c7182, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8191 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8191 : lratChecker f8191 p8191 = .success := by decide +kernel
theorem unsat8191 : Unsatisfiable (PosFin 65) f8191 := by
  apply lratCheckerSound f8191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8191
  · intro a ha; simp [p8191] at ha; subst a; trivial
  · exact checked8191
theorem derived8191 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8191 := by
  apply localUnsat_implies_entails f8191 [c8189, c8075, c8190, c6550, c6376, c7182] c8191 unsat8191 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c8190 := derived8190 a h
  have h3 : Entails.eval a c6550 := h 6549 (by decide)
  have h4 : Entails.eval a c6376 := h 6375 (by decide)
  have h5 : Entails.eval a c7182 := h 7181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8192 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨62, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8192 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c7126, some c6912, some c7391, some c6535, some c6805, some c7262, some c6698, some c6719, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8192 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8192 : lratChecker f8192 p8192 = .success := by decide +kernel
theorem unsat8192 : Unsatisfiable (PosFin 65) f8192 := by
  apply lratCheckerSound f8192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8192
  · intro a ha; simp [p8192] at ha; subst a; trivial
  · exact checked8192
theorem derived8192 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8192 := by
  apply localUnsat_implies_entails f8192 [c7132, c7126, c6912, c7391, c6535, c6805, c7262, c6698, c6719] c8192 unsat8192 (by rfl) a
  have h0 : Entails.eval a c7132 := h 7131 (by decide)
  have h1 : Entails.eval a c7126 := h 7125 (by decide)
  have h2 : Entails.eval a c6912 := h 6911 (by decide)
  have h3 : Entails.eval a c7391 := h 7390 (by decide)
  have h4 : Entails.eval a c6535 := h 6534 (by decide)
  have h5 : Entails.eval a c6805 := h 6804 (by decide)
  have h6 : Entails.eval a c7262 := h 7261 (by decide)
  have h7 : Entails.eval a c6698 := h 6697 (by decide)
  have h8 : Entails.eval a c6719 := h 6718 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8193 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨62, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8193 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8075, some c7994, some c8191, some c8192, some c6395, some c6364, some c6370, some c7439, some c7435, some c7441, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8193 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8193 : lratChecker f8193 p8193 = .success := by decide +kernel
theorem unsat8193 : Unsatisfiable (PosFin 65) f8193 := by
  apply lratCheckerSound f8193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8193
  · intro a ha; simp [p8193] at ha; subst a; trivial
  · exact checked8193
theorem derived8193 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8193 := by
  apply localUnsat_implies_entails f8193 [c8189, c8075, c7994, c8191, c8192, c6395, c6364, c6370, c7439, c7435, c7441] c8193 unsat8193 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8191 := derived8191 a h
  have h4 : Entails.eval a c8192 := derived8192 a h
  have h5 : Entails.eval a c6395 := h 6394 (by decide)
  have h6 : Entails.eval a c6364 := h 6363 (by decide)
  have h7 : Entails.eval a c6370 := h 6369 (by decide)
  have h8 : Entails.eval a c7439 := h 7438 (by decide)
  have h9 : Entails.eval a c7435 := h 7434 (by decide)
  have h10 : Entails.eval a c7441 := h 7440 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8194 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨34, by decide⟩, true), (⟨52, by decide⟩, true), (⟨48, by decide⟩, false), (⟨62, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8194 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7436, some c7540, some c6670, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8194 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8194 : lratChecker f8194 p8194 = .success := by decide +kernel
theorem unsat8194 : Unsatisfiable (PosFin 65) f8194 := by
  apply lratCheckerSound f8194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8194
  · intro a ha; simp [p8194] at ha; subst a; trivial
  · exact checked8194
theorem derived8194 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8194 := by
  apply localUnsat_implies_entails f8194 [c7436, c7540, c6670] c8194 unsat8194 (by rfl) a
  have h0 : Entails.eval a c7436 := h 7435 (by decide)
  have h1 : Entails.eval a c7540 := h 7539 (by decide)
  have h2 : Entails.eval a c6670 := h 6669 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8195 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8195 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8075, some c8193, some c8095, some c8189, some c6698, some c8194, some c6370, some c7168, some c6598, some c6805, some c7315, some c8082, some c6527, some c6519, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8195 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8195 : lratChecker f8195 p8195 = .success := by decide +kernel
theorem unsat8195 : Unsatisfiable (PosFin 65) f8195 := by
  apply lratCheckerSound f8195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8195
  · intro a ha; simp [p8195] at ha; subst a; trivial
  · exact checked8195
theorem derived8195 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8195 := by
  apply localUnsat_implies_entails f8195 [c7994, c8075, c8193, c8095, c8189, c6698, c8194, c6370, c7168, c6598, c6805, c7315, c8082, c6527, c6519] c8195 unsat8195 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c8193 := derived8193 a h
  have h3 : Entails.eval a c8095 := derived8095 a h
  have h4 : Entails.eval a c8189 := derived8189 a h
  have h5 : Entails.eval a c6698 := h 6697 (by decide)
  have h6 : Entails.eval a c8194 := derived8194 a h
  have h7 : Entails.eval a c6370 := h 6369 (by decide)
  have h8 : Entails.eval a c7168 := h 7167 (by decide)
  have h9 : Entails.eval a c6598 := h 6597 (by decide)
  have h10 : Entails.eval a c6805 := h 6804 (by decide)
  have h11 : Entails.eval a c7315 := h 7314 (by decide)
  have h12 : Entails.eval a c8082 := derived8082 a h
  have h13 : Entails.eval a c6527 := h 6526 (by decide)
  have h14 : Entails.eval a c6519 := h 6518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8196 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8196 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8160, some c8075, some c7994, some c8193, some c8095, some c8195, some c6426, some c7508, some c7510, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8196 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8196 : lratChecker f8196 p8196 = .success := by decide +kernel
theorem unsat8196 : Unsatisfiable (PosFin 65) f8196 := by
  apply lratCheckerSound f8196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8196
  · intro a ha; simp [p8196] at ha; subst a; trivial
  · exact checked8196
theorem derived8196 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8196 := by
  apply localUnsat_implies_entails f8196 [c8189, c8160, c8075, c7994, c8193, c8095, c8195, c6426, c7508, c7510] c8196 unsat8196 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8193 := derived8193 a h
  have h5 : Entails.eval a c8095 := derived8095 a h
  have h6 : Entails.eval a c8195 := derived8195 a h
  have h7 : Entails.eval a c6426 := h 6425 (by decide)
  have h8 : Entails.eval a c7508 := h 7507 (by decide)
  have h9 : Entails.eval a c7510 := h 7509 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8197 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8197 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8160, some c8075, some c6426, some c7182, some c7498, some c7152, some c6376, some c6863, some c7402, some c6583, some c7870, some c7258, some c6697, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8197 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8197 : lratChecker f8197 p8197 = .success := by decide +kernel
theorem unsat8197 : Unsatisfiable (PosFin 65) f8197 := by
  apply lratCheckerSound f8197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8197
  · intro a ha; simp [p8197] at ha; subst a; trivial
  · exact checked8197
theorem derived8197 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8197 := by
  apply localUnsat_implies_entails f8197 [c8189, c8160, c8075, c6426, c7182, c7498, c7152, c6376, c6863, c7402, c6583, c7870, c7258, c6697] c8197 unsat8197 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c6426 := h 6425 (by decide)
  have h4 : Entails.eval a c7182 := h 7181 (by decide)
  have h5 : Entails.eval a c7498 := h 7497 (by decide)
  have h6 : Entails.eval a c7152 := h 7151 (by decide)
  have h7 : Entails.eval a c6376 := h 6375 (by decide)
  have h8 : Entails.eval a c6863 := h 6862 (by decide)
  have h9 : Entails.eval a c7402 := h 7401 (by decide)
  have h10 : Entails.eval a c6583 := h 6582 (by decide)
  have h11 : Entails.eval a c7870 := derived7870 a h
  have h12 : Entails.eval a c7258 := h 7257 (by decide)
  have h13 : Entails.eval a c6697 := h 6696 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8198 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8198 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7504, some c7505, some c7495, some c7049, some c6979, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8198 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8198 : lratChecker f8198 p8198 = .success := by decide +kernel
theorem unsat8198 : Unsatisfiable (PosFin 65) f8198 := by
  apply lratCheckerSound f8198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8198
  · intro a ha; simp [p8198] at ha; subst a; trivial
  · exact checked8198
theorem derived8198 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8198 := by
  apply localUnsat_implies_entails f8198 [c7504, c7505, c7495, c7049, c6979] c8198 unsat8198 (by rfl) a
  have h0 : Entails.eval a c7504 := h 7503 (by decide)
  have h1 : Entails.eval a c7505 := h 7504 (by decide)
  have h2 : Entails.eval a c7495 := h 7494 (by decide)
  have h3 : Entails.eval a c7049 := h 7048 (by decide)
  have h4 : Entails.eval a c6979 := h 6978 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8199 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8199 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6425, some c6430, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8199 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8199 : lratChecker f8199 p8199 = .success := by decide +kernel
theorem unsat8199 : Unsatisfiable (PosFin 65) f8199 := by
  apply lratCheckerSound f8199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8199
  · intro a ha; simp [p8199] at ha; subst a; trivial
  · exact checked8199
theorem derived8199 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8199 := by
  apply localUnsat_implies_entails f8199 [c7994, c6425, c6430] c8199 unsat8199 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6425 := h 6424 (by decide)
  have h2 : Entails.eval a c6430 := h 6429 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8200 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8200 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8160, some c8075, some c8197, some c8199, some c8198, some c6435, some c6433, some c7499, some c7352, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8200 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8200 : lratChecker f8200 p8200 = .success := by decide +kernel
theorem unsat8200 : Unsatisfiable (PosFin 65) f8200 := by
  apply lratCheckerSound f8200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8200
  · intro a ha; simp [p8200] at ha; subst a; trivial
  · exact checked8200
theorem derived8200 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8200 := by
  apply localUnsat_implies_entails f8200 [c8189, c8160, c8075, c8197, c8199, c8198, c6435, c6433, c7499, c7352] c8200 unsat8200 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c8197 := derived8197 a h
  have h4 : Entails.eval a c8199 := derived8199 a h
  have h5 : Entails.eval a c8198 := derived8198 a h
  have h6 : Entails.eval a c6435 := h 6434 (by decide)
  have h7 : Entails.eval a c6433 := h 6432 (by decide)
  have h8 : Entails.eval a c7499 := h 7498 (by decide)
  have h9 : Entails.eval a c7352 := h 7351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8201 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨48, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8201 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8200, some c8191, some c8196, some c8189, some c8075, some c7186, some c6537, some c6968, some c6385, some c7031, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8201 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8201 : lratChecker f8201 p8201 = .success := by decide +kernel
theorem unsat8201 : Unsatisfiable (PosFin 65) f8201 := by
  apply lratCheckerSound f8201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8201
  · intro a ha; simp [p8201] at ha; subst a; trivial
  · exact checked8201
theorem derived8201 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8201 := by
  apply localUnsat_implies_entails f8201 [c8200, c8191, c8196, c8189, c8075, c7186, c6537, c6968, c6385, c7031] c8201 unsat8201 (by rfl) a
  have h0 : Entails.eval a c8200 := derived8200 a h
  have h1 : Entails.eval a c8191 := derived8191 a h
  have h2 : Entails.eval a c8196 := derived8196 a h
  have h3 : Entails.eval a c8189 := derived8189 a h
  have h4 : Entails.eval a c8075 := derived8075 a h
  have h5 : Entails.eval a c7186 := h 7185 (by decide)
  have h6 : Entails.eval a c6537 := h 6536 (by decide)
  have h7 : Entails.eval a c6968 := h 6967 (by decide)
  have h8 : Entails.eval a c6385 := h 6384 (by decide)
  have h9 : Entails.eval a c7031 := h 7030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8202 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8202 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7181, some c7257, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8202 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8202 : lratChecker f8202 p8202 = .success := by decide +kernel
theorem unsat8202 : Unsatisfiable (PosFin 65) f8202 := by
  apply lratCheckerSound f8202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8202
  · intro a ha; simp [p8202] at ha; subst a; trivial
  · exact checked8202
theorem derived8202 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8202 := by
  apply localUnsat_implies_entails f8202 [c7181, c7257] c8202 unsat8202 (by rfl) a
  have h0 : Entails.eval a c7181 := h 7180 (by decide)
  have h1 : Entails.eval a c7257 := h 7256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8203 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨48, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8203 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8200, some c8191, some c8196, some c8189, some c8075, some c7994, some c8202, some c7186, some c6400, some c6383, some c8201, some c7155, some c7275, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8203 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8203 : lratChecker f8203 p8203 = .success := by decide +kernel
theorem unsat8203 : Unsatisfiable (PosFin 65) f8203 := by
  apply lratCheckerSound f8203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8203
  · intro a ha; simp [p8203] at ha; subst a; trivial
  · exact checked8203
theorem derived8203 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8203 := by
  apply localUnsat_implies_entails f8203 [c8200, c8191, c8196, c8189, c8075, c7994, c8202, c7186, c6400, c6383, c8201, c7155, c7275] c8203 unsat8203 (by rfl) a
  have h0 : Entails.eval a c8200 := derived8200 a h
  have h1 : Entails.eval a c8191 := derived8191 a h
  have h2 : Entails.eval a c8196 := derived8196 a h
  have h3 : Entails.eval a c8189 := derived8189 a h
  have h4 : Entails.eval a c8075 := derived8075 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c8202 := derived8202 a h
  have h7 : Entails.eval a c7186 := h 7185 (by decide)
  have h8 : Entails.eval a c6400 := h 6399 (by decide)
  have h9 : Entails.eval a c6383 := h 6382 (by decide)
  have h10 : Entails.eval a c8201 := derived8201 a h
  have h11 : Entails.eval a c7155 := h 7154 (by decide)
  have h12 : Entails.eval a c7275 := h 7274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8204 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨48, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8204 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8200, some c8191, some c8189, some c8075, some c7994, some c8203, some c7497, some c7501, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8204 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8204 : lratChecker f8204 p8204 = .success := by decide +kernel
theorem unsat8204 : Unsatisfiable (PosFin 65) f8204 := by
  apply lratCheckerSound f8204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8204
  · intro a ha; simp [p8204] at ha; subst a; trivial
  · exact checked8204
theorem derived8204 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8204 := by
  apply localUnsat_implies_entails f8204 [c8200, c8191, c8189, c8075, c7994, c8203, c7497, c7501] c8204 unsat8204 (by rfl) a
  have h0 : Entails.eval a c8200 := derived8200 a h
  have h1 : Entails.eval a c8191 := derived8191 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8075 := derived8075 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c8203 := derived8203 a h
  have h6 : Entails.eval a c7497 := h 7496 (by decide)
  have h7 : Entails.eval a c7501 := h 7500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8205 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8205 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8196, some c8189, some c8075, some c6688, some c6556, some c6755, some c7550, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8205 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8205 : lratChecker f8205 p8205 = .success := by decide +kernel
theorem unsat8205 : Unsatisfiable (PosFin 65) f8205 := by
  apply lratCheckerSound f8205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8205
  · intro a ha; simp [p8205] at ha; subst a; trivial
  · exact checked8205
theorem derived8205 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8205 := by
  apply localUnsat_implies_entails f8205 [c8196, c8189, c8075, c6688, c6556, c6755, c7550] c8205 unsat8205 (by rfl) a
  have h0 : Entails.eval a c8196 := derived8196 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c6688 := h 6687 (by decide)
  have h4 : Entails.eval a c6556 := h 6555 (by decide)
  have h5 : Entails.eval a c6755 := h 6754 (by decide)
  have h6 : Entails.eval a c7550 := h 7549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8206 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8206 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8200, some c8191, some c8189, some c7994, some c8205, some c6519, some c7486, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8206 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8206 : lratChecker f8206 p8206 = .success := by decide +kernel
theorem unsat8206 : Unsatisfiable (PosFin 65) f8206 := by
  apply lratCheckerSound f8206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8206
  · intro a ha; simp [p8206] at ha; subst a; trivial
  · exact checked8206
theorem derived8206 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8206 := by
  apply localUnsat_implies_entails f8206 [c8200, c8191, c8189, c7994, c8205, c6519, c7486] c8206 unsat8206 (by rfl) a
  have h0 : Entails.eval a c8200 := derived8200 a h
  have h1 : Entails.eval a c8191 := derived8191 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8205 := derived8205 a h
  have h5 : Entails.eval a c6519 := h 6518 (by decide)
  have h6 : Entails.eval a c7486 := h 7485 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8207 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8207 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6519, some c7257, some c7138, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8207 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8207 : lratChecker f8207 p8207 = .success := by decide +kernel
theorem unsat8207 : Unsatisfiable (PosFin 65) f8207 := by
  apply lratCheckerSound f8207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8207
  · intro a ha; simp [p8207] at ha; subst a; trivial
  · exact checked8207
theorem derived8207 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8207 := by
  apply localUnsat_implies_entails f8207 [c6519, c7257, c7138] c8207 unsat8207 (by rfl) a
  have h0 : Entails.eval a c6519 := h 6518 (by decide)
  have h1 : Entails.eval a c7257 := h 7256 (by decide)
  have h2 : Entails.eval a c7138 := h 7137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8208 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8208 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8200, some c8191, some c8075, some c7994, some c8204, some c8206, some c8207, some c6556, some c6527, some c7365, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8208 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8208 : lratChecker f8208 p8208 = .success := by decide +kernel
theorem unsat8208 : Unsatisfiable (PosFin 65) f8208 := by
  apply lratCheckerSound f8208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8208
  · intro a ha; simp [p8208] at ha; subst a; trivial
  · exact checked8208
theorem derived8208 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8208 := by
  apply localUnsat_implies_entails f8208 [c8200, c8191, c8075, c7994, c8204, c8206, c8207, c6556, c6527, c7365] c8208 unsat8208 (by rfl) a
  have h0 : Entails.eval a c8200 := derived8200 a h
  have h1 : Entails.eval a c8191 := derived8191 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8204 := derived8204 a h
  have h5 : Entails.eval a c8206 := derived8206 a h
  have h6 : Entails.eval a c8207 := derived8207 a h
  have h7 : Entails.eval a c6556 := h 6555 (by decide)
  have h8 : Entails.eval a c6527 := h 6526 (by decide)
  have h9 : Entails.eval a c7365 := h 7364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8209 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨46, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8209 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6556, some c6527, some c7365, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8209 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8209 : lratChecker f8209 p8209 = .success := by decide +kernel
theorem unsat8209 : Unsatisfiable (PosFin 65) f8209 := by
  apply lratCheckerSound f8209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8209
  · intro a ha; simp [p8209] at ha; subst a; trivial
  · exact checked8209
theorem derived8209 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8209 := by
  apply localUnsat_implies_entails f8209 [c6556, c6527, c7365] c8209 unsat8209 (by rfl) a
  have h0 : Entails.eval a c6556 := h 6555 (by decide)
  have h1 : Entails.eval a c6527 := h 6526 (by decide)
  have h2 : Entails.eval a c7365 := h 7364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8210 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8210 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8208, some c8200, some c8191, some c8196, some c8189, some c8160, some c8075, some c7994, some c8209, some c6696, some c6519, some c7138, some c7303, some c6635, some c6639, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8210 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8210 : lratChecker f8210 p8210 = .success := by decide +kernel
theorem unsat8210 : Unsatisfiable (PosFin 65) f8210 := by
  apply lratCheckerSound f8210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8210
  · intro a ha; simp [p8210] at ha; subst a; trivial
  · exact checked8210
theorem derived8210 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8210 := by
  apply localUnsat_implies_entails f8210 [c8208, c8200, c8191, c8196, c8189, c8160, c8075, c7994, c8209, c6696, c6519, c7138, c7303, c6635, c6639] c8210 unsat8210 (by rfl) a
  have h0 : Entails.eval a c8208 := derived8208 a h
  have h1 : Entails.eval a c8200 := derived8200 a h
  have h2 : Entails.eval a c8191 := derived8191 a h
  have h3 : Entails.eval a c8196 := derived8196 a h
  have h4 : Entails.eval a c8189 := derived8189 a h
  have h5 : Entails.eval a c8160 := derived8160 a h
  have h6 : Entails.eval a c8075 := derived8075 a h
  have h7 : Entails.eval a c7994 := derived7994 a h
  have h8 : Entails.eval a c8209 := derived8209 a h
  have h9 : Entails.eval a c6696 := h 6695 (by decide)
  have h10 : Entails.eval a c6519 := h 6518 (by decide)
  have h11 : Entails.eval a c7138 := h 7137 (by decide)
  have h12 : Entails.eval a c7303 := h 7302 (by decide)
  have h13 : Entails.eval a c6635 := h 6634 (by decide)
  have h14 : Entails.eval a c6639 := h 6638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8211 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8211 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8075, some c8200, some c8191, some c8208, some c8210, some c7504, some c7505, some c7509, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8211 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8211 : lratChecker f8211 p8211 = .success := by decide +kernel
theorem unsat8211 : Unsatisfiable (PosFin 65) f8211 := by
  apply lratCheckerSound f8211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8211
  · intro a ha; simp [p8211] at ha; subst a; trivial
  · exact checked8211
theorem derived8211 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8211 := by
  apply localUnsat_implies_entails f8211 [c8189, c8075, c8200, c8191, c8208, c8210, c7504, c7505, c7509] c8211 unsat8211 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c8200 := derived8200 a h
  have h3 : Entails.eval a c8191 := derived8191 a h
  have h4 : Entails.eval a c8208 := derived8208 a h
  have h5 : Entails.eval a c8210 := derived8210 a h
  have h6 : Entails.eval a c7504 := h 7503 (by decide)
  have h7 : Entails.eval a c7505 := h 7504 (by decide)
  have h8 : Entails.eval a c7509 := h 7508 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8212 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8212 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7508, some c7506, some c7512, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8212 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8212 : lratChecker f8212 p8212 = .success := by decide +kernel
theorem unsat8212 : Unsatisfiable (PosFin 65) f8212 := by
  apply lratCheckerSound f8212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8212
  · intro a ha; simp [p8212] at ha; subst a; trivial
  · exact checked8212
theorem derived8212 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8212 := by
  apply localUnsat_implies_entails f8212 [c7508, c7506, c7512] c8212 unsat8212 (by rfl) a
  have h0 : Entails.eval a c7508 := h 7507 (by decide)
  have h1 : Entails.eval a c7506 := h 7505 (by decide)
  have h2 : Entails.eval a c7512 := h 7511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8213 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8213 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8189, some c7499, some c8160, some c8212, some c7994, some c8202, some c7186, some c7249, some c7155, some c7282, some c7403, some c7224, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8213 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8213 : lratChecker f8213 p8213 = .success := by decide +kernel
theorem unsat8213 : Unsatisfiable (PosFin 65) f8213 := by
  apply lratCheckerSound f8213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8213
  · intro a ha; simp [p8213] at ha; subst a; trivial
  · exact checked8213
theorem derived8213 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8213 := by
  apply localUnsat_implies_entails f8213 [c8075, c8189, c7499, c8160, c8212, c7994, c8202, c7186, c7249, c7155, c7282, c7403, c7224] c8213 unsat8213 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c7499 := h 7498 (by decide)
  have h3 : Entails.eval a c8160 := derived8160 a h
  have h4 : Entails.eval a c8212 := derived8212 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c8202 := derived8202 a h
  have h7 : Entails.eval a c7186 := h 7185 (by decide)
  have h8 : Entails.eval a c7249 := h 7248 (by decide)
  have h9 : Entails.eval a c7155 := h 7154 (by decide)
  have h10 : Entails.eval a c7282 := h 7281 (by decide)
  have h11 : Entails.eval a c7403 := h 7402 (by decide)
  have h12 : Entails.eval a c7224 := h 7223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8214 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8214 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8075, some c8160, some c8189, some c8212, some c7499, some c8213, some c7182, some c7258, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8214 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8214 : lratChecker f8214 p8214 = .success := by decide +kernel
theorem unsat8214 : Unsatisfiable (PosFin 65) f8214 := by
  apply lratCheckerSound f8214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8214
  · intro a ha; simp [p8214] at ha; subst a; trivial
  · exact checked8214
theorem derived8214 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8214 := by
  apply localUnsat_implies_entails f8214 [c8075, c8160, c8189, c8212, c7499, c8213, c7182, c7258] c8214 unsat8214 (by rfl) a
  have h0 : Entails.eval a c8075 := derived8075 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8212 := derived8212 a h
  have h4 : Entails.eval a c7499 := h 7498 (by decide)
  have h5 : Entails.eval a c8213 := derived8213 a h
  have h6 : Entails.eval a c7182 := h 7181 (by decide)
  have h7 : Entails.eval a c7258 := h 7257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8215 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨48, by decide⟩, true), (⟨46, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8215 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7491, some c7176, some c7251, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8215 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8215 : lratChecker f8215 p8215 = .success := by decide +kernel
theorem unsat8215 : Unsatisfiable (PosFin 65) f8215 := by
  apply lratCheckerSound f8215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8215
  · intro a ha; simp [p8215] at ha; subst a; trivial
  · exact checked8215
theorem derived8215 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8215 := by
  apply localUnsat_implies_entails f8215 [c7491, c7176, c7251] c8215 unsat8215 (by rfl) a
  have h0 : Entails.eval a c7491 := h 7490 (by decide)
  have h1 : Entails.eval a c7176 := h 7175 (by decide)
  have h2 : Entails.eval a c7251 := h 7250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8216 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8216 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8160, some c8189, some c8075, some c8212, some c8215, some c8214, some c7490, some c7994, some c7258, some c7257, some c7248, some c7155, some c6850, some c6917, some c7261, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8216 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8216 : lratChecker f8216 p8216 = .success := by decide +kernel
theorem unsat8216 : Unsatisfiable (PosFin 65) f8216 := by
  apply lratCheckerSound f8216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8216
  · intro a ha; simp [p8216] at ha; subst a; trivial
  · exact checked8216
theorem derived8216 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8216 := by
  apply localUnsat_implies_entails f8216 [c8160, c8189, c8075, c8212, c8215, c8214, c7490, c7994, c7258, c7257, c7248, c7155, c6850, c6917, c7261] c8216 unsat8216 (by rfl) a
  have h0 : Entails.eval a c8160 := derived8160 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c8212 := derived8212 a h
  have h4 : Entails.eval a c8215 := derived8215 a h
  have h5 : Entails.eval a c8214 := derived8214 a h
  have h6 : Entails.eval a c7490 := h 7489 (by decide)
  have h7 : Entails.eval a c7994 := derived7994 a h
  have h8 : Entails.eval a c7258 := h 7257 (by decide)
  have h9 : Entails.eval a c7257 := h 7256 (by decide)
  have h10 : Entails.eval a c7248 := h 7247 (by decide)
  have h11 : Entails.eval a c7155 := h 7154 (by decide)
  have h12 : Entails.eval a c6850 := h 6849 (by decide)
  have h13 : Entails.eval a c6917 := h 6916 (by decide)
  have h14 : Entails.eval a c7261 := h 7260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8217 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8217 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8075, some c7994, some c7182, some c7186, some c7181, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8217 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8217 : lratChecker f8217 p8217 = .success := by decide +kernel
theorem unsat8217 : Unsatisfiable (PosFin 65) f8217 := by
  apply lratCheckerSound f8217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8217
  · intro a ha; simp [p8217] at ha; subst a; trivial
  · exact checked8217
theorem derived8217 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8217 := by
  apply localUnsat_implies_entails f8217 [c8189, c8075, c7994, c7182, c7186, c7181] c8217 unsat8217 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c7182 := h 7181 (by decide)
  have h4 : Entails.eval a c7186 := h 7185 (by decide)
  have h5 : Entails.eval a c7181 := h 7180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8218 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨46, by decide⟩, false), (⟨40, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8218 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7347, some c7497, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8218 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8218 : lratChecker f8218 p8218 = .success := by decide +kernel
theorem unsat8218 : Unsatisfiable (PosFin 65) f8218 := by
  apply lratCheckerSound f8218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8218
  · intro a ha; simp [p8218] at ha; subst a; trivial
  · exact checked8218
theorem derived8218 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8218 := by
  apply localUnsat_implies_entails f8218 [c7347, c7497] c8218 unsat8218 (by rfl) a
  have h0 : Entails.eval a c7347 := h 7346 (by decide)
  have h1 : Entails.eval a c7497 := h 7496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8219 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8219 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8217, some c8216, some c8075, some c8160, some c8189, some c8212, some c7501, some c7350, some c7339, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8219 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8219 : lratChecker f8219 p8219 = .success := by decide +kernel
theorem unsat8219 : Unsatisfiable (PosFin 65) f8219 := by
  apply lratCheckerSound f8219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8219
  · intro a ha; simp [p8219] at ha; subst a; trivial
  · exact checked8219
theorem derived8219 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8219 := by
  apply localUnsat_implies_entails f8219 [c8217, c8216, c8075, c8160, c8189, c8212, c7501, c7350, c7339] c8219 unsat8219 (by rfl) a
  have h0 : Entails.eval a c8217 := derived8217 a h
  have h1 : Entails.eval a c8216 := derived8216 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c8160 := derived8160 a h
  have h4 : Entails.eval a c8189 := derived8189 a h
  have h5 : Entails.eval a c8212 := derived8212 a h
  have h6 : Entails.eval a c7501 := h 7500 (by decide)
  have h7 : Entails.eval a c7350 := h 7349 (by decide)
  have h8 : Entails.eval a c7339 := h 7338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8220 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8220 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8160, some c8075, some c7994, some c8212, some c8215, some c8217, some c8216, some c8219, some c8218, some c7498, some c7258, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8220 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8220 : lratChecker f8220 p8220 = .success := by decide +kernel
theorem unsat8220 : Unsatisfiable (PosFin 65) f8220 := by
  apply lratCheckerSound f8220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8220
  · intro a ha; simp [p8220] at ha; subst a; trivial
  · exact checked8220
theorem derived8220 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8220 := by
  apply localUnsat_implies_entails f8220 [c8189, c8160, c8075, c7994, c8212, c8215, c8217, c8216, c8219, c8218, c7498, c7258] c8220 unsat8220 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8212 := derived8212 a h
  have h5 : Entails.eval a c8215 := derived8215 a h
  have h6 : Entails.eval a c8217 := derived8217 a h
  have h7 : Entails.eval a c8216 := derived8216 a h
  have h8 : Entails.eval a c8219 := derived8219 a h
  have h9 : Entails.eval a c8218 := derived8218 a h
  have h10 : Entails.eval a c7498 := h 7497 (by decide)
  have h11 : Entails.eval a c7258 := h 7257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8221 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨48, by decide⟩, true), (⟨57, by decide⟩, true), (⟨52, by decide⟩, false), (⟨38, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8221 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7348, some c7353, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p8221 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8221 : lratChecker f8221 p8221 = .success := by decide +kernel
theorem unsat8221 : Unsatisfiable (PosFin 65) f8221 := by
  apply lratCheckerSound f8221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8221
  · intro a ha; simp [p8221] at ha; subst a; trivial
  · exact checked8221
theorem derived8221 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8221 := by
  apply localUnsat_implies_entails f8221 [c7348, c7353] c8221 unsat8221 (by rfl) a
  have h0 : Entails.eval a c7348 := h 7347 (by decide)
  have h1 : Entails.eval a c7353 := h 7352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8222 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8222 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8211, some c8189, some c8075, some c7487, some c6682, some c6321, some c6597, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8222 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8222 : lratChecker f8222 p8222 = .success := by decide +kernel
theorem unsat8222 : Unsatisfiable (PosFin 65) f8222 := by
  apply lratCheckerSound f8222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8222
  · intro a ha; simp [p8222] at ha; subst a; trivial
  · exact checked8222
theorem derived8222 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8222 := by
  apply localUnsat_implies_entails f8222 [c8211, c8189, c8075, c7487, c6682, c6321, c6597] c8222 unsat8222 (by rfl) a
  have h0 : Entails.eval a c8211 := derived8211 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c7487 := h 7486 (by decide)
  have h4 : Entails.eval a c6682 := h 6681 (by decide)
  have h5 : Entails.eval a c6321 := h 6320 (by decide)
  have h6 : Entails.eval a c6597 := h 6596 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8223 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8223 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8211, some c8075, some c6597, some c6911, some c6278, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8223 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8223 : lratChecker f8223 p8223 = .success := by decide +kernel
theorem unsat8223 : Unsatisfiable (PosFin 65) f8223 := by
  apply lratCheckerSound f8223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8223
  · intro a ha; simp [p8223] at ha; subst a; trivial
  · exact checked8223
theorem derived8223 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8223 := by
  apply localUnsat_implies_entails f8223 [c8211, c8075, c6597, c6911, c6278] c8223 unsat8223 (by rfl) a
  have h0 : Entails.eval a c8211 := derived8211 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c6597 := h 6596 (by decide)
  have h3 : Entails.eval a c6911 := h 6910 (by decide)
  have h4 : Entails.eval a c6278 := h 6277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8224 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨48, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8224 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6697, some c6700, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p8224 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8224 : lratChecker f8224 p8224 = .success := by decide +kernel
theorem unsat8224 : Unsatisfiable (PosFin 65) f8224 := by
  apply lratCheckerSound f8224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8224
  · intro a ha; simp [p8224] at ha; subst a; trivial
  · exact checked8224
theorem derived8224 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8224 := by
  apply localUnsat_implies_entails f8224 [c6697, c6700] c8224 unsat8224 (by rfl) a
  have h0 : Entails.eval a c6697 := h 6696 (by decide)
  have h1 : Entails.eval a c6700 := h 6699 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8225 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨48, by decide⟩, false), (⟨38, by decide⟩, true), (⟨46, by decide⟩, true), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8225 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6984, some c7045, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8225 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8225 : lratChecker f8225 p8225 = .success := by decide +kernel
theorem unsat8225 : Unsatisfiable (PosFin 65) f8225 := by
  apply lratCheckerSound f8225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8225
  · intro a ha; simp [p8225] at ha; subst a; trivial
  · exact checked8225
theorem derived8225 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8225 := by
  apply localUnsat_implies_entails f8225 [c6984, c7045] c8225 unsat8225 (by rfl) a
  have h0 : Entails.eval a c6984 := h 6983 (by decide)
  have h1 : Entails.eval a c7045 := h 7044 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8226 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨45, by decide⟩, false), (⟨61, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8226 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7025, some c7016, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8226 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8226 : lratChecker f8226 p8226 = .success := by decide +kernel
theorem unsat8226 : Unsatisfiable (PosFin 65) f8226 := by
  apply lratCheckerSound f8226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8226
  · intro a ha; simp [p8226] at ha; subst a; trivial
  · exact checked8226
theorem derived8226 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8226 := by
  apply localUnsat_implies_entails f8226 [c7025, c7016] c8226 unsat8226 (by rfl) a
  have h0 : Entails.eval a c7025 := h 7024 (by decide)
  have h1 : Entails.eval a c7016 := h 7015 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8227 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨57, by decide⟩, true), (⟨52, by decide⟩, false), (⟨38, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8227 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8160, some c8189, some c8220, some c8075, some c8222, some c8221, some c8225, some c8224, some c8211, some c7994, some c8223, some c7167, some c7152, some c6632, some c6492, some c8226, some c6769, some c6967, some c6786, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8227 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8227 : lratChecker f8227 p8227 = .success := by decide +kernel
theorem unsat8227 : Unsatisfiable (PosFin 65) f8227 := by
  apply lratCheckerSound f8227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8227
  · intro a ha; simp [p8227] at ha; subst a; trivial
  · exact checked8227
theorem derived8227 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8227 := by
  apply localUnsat_implies_entails f8227 [c8160, c8189, c8220, c8075, c8222, c8221, c8225, c8224, c8211, c7994, c8223, c7167, c7152, c6632, c6492, c8226, c6769, c6967, c6786] c8227 unsat8227 (by rfl) a
  have h0 : Entails.eval a c8160 := derived8160 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c8220 := derived8220 a h
  have h3 : Entails.eval a c8075 := derived8075 a h
  have h4 : Entails.eval a c8222 := derived8222 a h
  have h5 : Entails.eval a c8221 := derived8221 a h
  have h6 : Entails.eval a c8225 := derived8225 a h
  have h7 : Entails.eval a c8224 := derived8224 a h
  have h8 : Entails.eval a c8211 := derived8211 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c8223 := derived8223 a h
  have h11 : Entails.eval a c7167 := h 7166 (by decide)
  have h12 : Entails.eval a c7152 := h 7151 (by decide)
  have h13 : Entails.eval a c6632 := h 6631 (by decide)
  have h14 : Entails.eval a c6492 := h 6491 (by decide)
  have h15 : Entails.eval a c8226 := derived8226 a h
  have h16 : Entails.eval a c6769 := h 6768 (by decide)
  have h17 : Entails.eval a c6967 := h 6966 (by decide)
  have h18 : Entails.eval a c6786 := h 6785 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8228 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨52, by decide⟩, false), (⟨38, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8228 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8222, some c8220, some c8189, some c8160, some c8075, some c7994, some c8221, some c8224, some c8225, some c8227, some c6750, some c7167, some c7152, some c6863, some c8226, some c6967, some c6622, some c6973, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8228 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8228 : lratChecker f8228 p8228 = .success := by decide +kernel
theorem unsat8228 : Unsatisfiable (PosFin 65) f8228 := by
  apply lratCheckerSound f8228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8228
  · intro a ha; simp [p8228] at ha; subst a; trivial
  · exact checked8228
theorem derived8228 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8228 := by
  apply localUnsat_implies_entails f8228 [c8222, c8220, c8189, c8160, c8075, c7994, c8221, c8224, c8225, c8227, c6750, c7167, c7152, c6863, c8226, c6967, c6622, c6973] c8228 unsat8228 (by rfl) a
  have h0 : Entails.eval a c8222 := derived8222 a h
  have h1 : Entails.eval a c8220 := derived8220 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8160 := derived8160 a h
  have h4 : Entails.eval a c8075 := derived8075 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c8221 := derived8221 a h
  have h7 : Entails.eval a c8224 := derived8224 a h
  have h8 : Entails.eval a c8225 := derived8225 a h
  have h9 : Entails.eval a c8227 := derived8227 a h
  have h10 : Entails.eval a c6750 := h 6749 (by decide)
  have h11 : Entails.eval a c7167 := h 7166 (by decide)
  have h12 : Entails.eval a c7152 := h 7151 (by decide)
  have h13 : Entails.eval a c6863 := h 6862 (by decide)
  have h14 : Entails.eval a c8226 := derived8226 a h
  have h15 : Entails.eval a c6967 := h 6966 (by decide)
  have h16 : Entails.eval a c6622 := h 6621 (by decide)
  have h17 : Entails.eval a c6973 := h 6972 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8229 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨36, by decide⟩, false), (⟨57, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8229 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7042, some c7052, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8229 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8229 : lratChecker f8229 p8229 = .success := by decide +kernel
theorem unsat8229 : Unsatisfiable (PosFin 65) f8229 := by
  apply lratCheckerSound f8229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8229
  · intro a ha; simp [p8229] at ha; subst a; trivial
  · exact checked8229
theorem derived8229 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8229 := by
  apply localUnsat_implies_entails f8229 [c7042, c7052] c8229 unsat8229 (by rfl) a
  have h0 : Entails.eval a c7042 := h 7041 (by decide)
  have h1 : Entails.eval a c7052 := h 7051 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8230 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨38, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8230 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8189, some c8160, some c8075, some c8222, some c8228, some c6982, some c8229, some c7348, some c7341, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8230 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8230 : lratChecker f8230 p8230 = .success := by decide +kernel
theorem unsat8230 : Unsatisfiable (PosFin 65) f8230 := by
  apply lratCheckerSound f8230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8230
  · intro a ha; simp [p8230] at ha; subst a; trivial
  · exact checked8230
theorem derived8230 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8230 := by
  apply localUnsat_implies_entails f8230 [c8189, c8160, c8075, c8222, c8228, c6982, c8229, c7348, c7341] c8230 unsat8230 (by rfl) a
  have h0 : Entails.eval a c8189 := derived8189 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8075 := derived8075 a h
  have h3 : Entails.eval a c8222 := derived8222 a h
  have h4 : Entails.eval a c8228 := derived8228 a h
  have h5 : Entails.eval a c6982 := h 6981 (by decide)
  have h6 : Entails.eval a c8229 := derived8229 a h
  have h7 : Entails.eval a c7348 := h 7347 (by decide)
  have h8 : Entails.eval a c7341 := h 7340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8231 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨38, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8231 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8230, some c8220, some c8189, some c8160, some c8075, some c7994, some c6989, some c7036, some c8229, some c6755, some c6687, some c7346, some c7350, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8231 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8231 : lratChecker f8231 p8231 = .success := by decide +kernel
theorem unsat8231 : Unsatisfiable (PosFin 65) f8231 := by
  apply lratCheckerSound f8231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8231
  · intro a ha; simp [p8231] at ha; subst a; trivial
  · exact checked8231
theorem derived8231 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8231 := by
  apply localUnsat_implies_entails f8231 [c8230, c8220, c8189, c8160, c8075, c7994, c6989, c7036, c8229, c6755, c6687, c7346, c7350] c8231 unsat8231 (by rfl) a
  have h0 : Entails.eval a c8230 := derived8230 a h
  have h1 : Entails.eval a c8220 := derived8220 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8160 := derived8160 a h
  have h4 : Entails.eval a c8075 := derived8075 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c6989 := h 6988 (by decide)
  have h7 : Entails.eval a c7036 := h 7035 (by decide)
  have h8 : Entails.eval a c8229 := derived8229 a h
  have h9 : Entails.eval a c6755 := h 6754 (by decide)
  have h10 : Entails.eval a c6687 := h 6686 (by decide)
  have h11 : Entails.eval a c7346 := h 7345 (by decide)
  have h12 : Entails.eval a c7350 := h 7349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8232 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8232 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8220, some c8211, some c8189, some c8160, some c8075, some c7994, some c8230, some c8231, some c7330, some c6307, some c6843, some c6696, some c8225, some c6749, some c7486, some c7166, some c7151, some c8226, some c6967, some c6622, some c6987, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8232 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8232 : lratChecker f8232 p8232 = .success := by decide +kernel
theorem unsat8232 : Unsatisfiable (PosFin 65) f8232 := by
  apply lratCheckerSound f8232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8232
  · intro a ha; simp [p8232] at ha; subst a; trivial
  · exact checked8232
theorem derived8232 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8232 := by
  apply localUnsat_implies_entails f8232 [c8220, c8211, c8189, c8160, c8075, c7994, c8230, c8231, c7330, c6307, c6843, c6696, c8225, c6749, c7486, c7166, c7151, c8226, c6967, c6622, c6987] c8232 unsat8232 (by rfl) a
  have h0 : Entails.eval a c8220 := derived8220 a h
  have h1 : Entails.eval a c8211 := derived8211 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8160 := derived8160 a h
  have h4 : Entails.eval a c8075 := derived8075 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c8230 := derived8230 a h
  have h7 : Entails.eval a c8231 := derived8231 a h
  have h8 : Entails.eval a c7330 := h 7329 (by decide)
  have h9 : Entails.eval a c6307 := h 6306 (by decide)
  have h10 : Entails.eval a c6843 := h 6842 (by decide)
  have h11 : Entails.eval a c6696 := h 6695 (by decide)
  have h12 : Entails.eval a c8225 := derived8225 a h
  have h13 : Entails.eval a c6749 := h 6748 (by decide)
  have h14 : Entails.eval a c7486 := h 7485 (by decide)
  have h15 : Entails.eval a c7166 := h 7165 (by decide)
  have h16 : Entails.eval a c7151 := h 7150 (by decide)
  have h17 : Entails.eval a c8226 := derived8226 a h
  have h18 : Entails.eval a c6967 := h 6966 (by decide)
  have h19 : Entails.eval a c6622 := h 6621 (by decide)
  have h20 : Entails.eval a c6987 := h 6986 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8233 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8233 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6734, some c6749, some c6307, some c7303, some c6582, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8233 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8233 : lratChecker f8233 p8233 = .success := by decide +kernel
theorem unsat8233 : Unsatisfiable (PosFin 65) f8233 := by
  apply lratCheckerSound f8233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8233
  · intro a ha; simp [p8233] at ha; subst a; trivial
  · exact checked8233
theorem derived8233 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8233 := by
  apply localUnsat_implies_entails f8233 [c6734, c6749, c6307, c7303, c6582] c8233 unsat8233 (by rfl) a
  have h0 : Entails.eval a c6734 := h 6733 (by decide)
  have h1 : Entails.eval a c6749 := h 6748 (by decide)
  have h2 : Entails.eval a c6307 := h 6306 (by decide)
  have h3 : Entails.eval a c7303 := h 7302 (by decide)
  have h4 : Entails.eval a c6582 := h 6581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8234 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨36, by decide⟩, true), (⟨39, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8234 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7279, some c7114, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p8234 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8234 : lratChecker f8234 p8234 = .success := by decide +kernel
theorem unsat8234 : Unsatisfiable (PosFin 65) f8234 := by
  apply lratCheckerSound f8234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8234
  · intro a ha; simp [p8234] at ha; subst a; trivial
  · exact checked8234
theorem derived8234 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8234 := by
  apply localUnsat_implies_entails f8234 [c7279, c7114] c8234 unsat8234 (by rfl) a
  have h0 : Entails.eval a c7279 := h 7278 (by decide)
  have h1 : Entails.eval a c7114 := h 7113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8235 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨61, by decide⟩, false), (⟨60, by decide⟩, false), (⟨36, by decide⟩, true), (⟨39, by decide⟩, false), (⟨35, by decide⟩, false), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8235 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6866, some c7116, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p8235 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8235 : lratChecker f8235 p8235 = .success := by decide +kernel
theorem unsat8235 : Unsatisfiable (PosFin 65) f8235 := by
  apply lratCheckerSound f8235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8235
  · intro a ha; simp [p8235] at ha; subst a; trivial
  · exact checked8235
theorem derived8235 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8235 := by
  apply localUnsat_implies_entails f8235 [c6866, c7116] c8235 unsat8235 (by rfl) a
  have h0 : Entails.eval a c6866 := h 6865 (by decide)
  have h1 : Entails.eval a c7116 := h 7115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8236 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨36, by decide⟩, true), (⟨39, by decide⟩, false), (⟨57, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8236 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8232, some c8220, some c8160, some c8185, some c7113, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8236 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8236 : lratChecker f8236 p8236 = .success := by decide +kernel
theorem unsat8236 : Unsatisfiable (PosFin 65) f8236 := by
  apply lratCheckerSound f8236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8236
  · intro a ha; simp [p8236] at ha; subst a; trivial
  · exact checked8236
theorem derived8236 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8236 := by
  apply localUnsat_implies_entails f8236 [c8232, c8220, c8160, c8185, c7113] c8236 unsat8236 (by rfl) a
  have h0 : Entails.eval a c8232 := derived8232 a h
  have h1 : Entails.eval a c8220 := derived8220 a h
  have h2 : Entails.eval a c8160 := derived8160 a h
  have h3 : Entails.eval a c8185 := derived8185 a h
  have h4 : Entails.eval a c7113 := h 7112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8237 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8237 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8189, some c8211, some c8220, some c8232, some c8233, some c6681, some c6696, some c7257, some c7166, some c6952, some c6307, some c7418, some c8160, some c8234, some c8236, some c8235, some c7120, some c7064, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8237 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8237 : lratChecker f8237 p8237 = .success := by decide +kernel
theorem unsat8237 : Unsatisfiable (PosFin 65) f8237 := by
  apply lratCheckerSound f8237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8237
  · intro a ha; simp [p8237] at ha; subst a; trivial
  · exact checked8237
theorem derived8237 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8237 := by
  apply localUnsat_implies_entails f8237 [c7994, c8189, c8211, c8220, c8232, c8233, c6681, c6696, c7257, c7166, c6952, c6307, c7418, c8160, c8234, c8236, c8235, c7120, c7064] c8237 unsat8237 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8189 := derived8189 a h
  have h2 : Entails.eval a c8211 := derived8211 a h
  have h3 : Entails.eval a c8220 := derived8220 a h
  have h4 : Entails.eval a c8232 := derived8232 a h
  have h5 : Entails.eval a c8233 := derived8233 a h
  have h6 : Entails.eval a c6681 := h 6680 (by decide)
  have h7 : Entails.eval a c6696 := h 6695 (by decide)
  have h8 : Entails.eval a c7257 := h 7256 (by decide)
  have h9 : Entails.eval a c7166 := h 7165 (by decide)
  have h10 : Entails.eval a c6952 := h 6951 (by decide)
  have h11 : Entails.eval a c6307 := h 6306 (by decide)
  have h12 : Entails.eval a c7418 := h 7417 (by decide)
  have h13 : Entails.eval a c8160 := derived8160 a h
  have h14 : Entails.eval a c8234 := derived8234 a h
  have h15 : Entails.eval a c8236 := derived8236 a h
  have h16 : Entails.eval a c8235 := derived8235 a h
  have h17 : Entails.eval a c7120 := h 7119 (by decide)
  have h18 : Entails.eval a c7064 := h 7063 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8238 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨61, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8238 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c419, some c472, some c1519, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8238 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8238 : lratChecker f8238 p8238 = .success := by decide +kernel
theorem unsat8238 : Unsatisfiable (PosFin 65) f8238 := by
  apply lratCheckerSound f8238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8238
  · intro a ha; simp [p8238] at ha; subst a; trivial
  · exact checked8238
theorem derived8238 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8238 := by
  apply localUnsat_implies_entails f8238 [c419, c472, c1519] c8238 unsat8238 (by rfl) a
  have h0 : Entails.eval a c419 := h 418 (by decide)
  have h1 : Entails.eval a c472 := h 471 (by decide)
  have h2 : Entails.eval a c1519 := h 1518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8239 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, true), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8239 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6681, some c6696, some c7257, some c7166, some c6952, some c6307, some c7418, some c8124, some c419, some c412, some c436, some c2410, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8239 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8239 : lratChecker f8239 p8239 = .success := by decide +kernel
theorem unsat8239 : Unsatisfiable (PosFin 65) f8239 := by
  apply lratCheckerSound f8239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8239
  · intro a ha; simp [p8239] at ha; subst a; trivial
  · exact checked8239
theorem derived8239 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8239 := by
  apply localUnsat_implies_entails f8239 [c6681, c6696, c7257, c7166, c6952, c6307, c7418, c8124, c419, c412, c436, c2410] c8239 unsat8239 (by rfl) a
  have h0 : Entails.eval a c6681 := h 6680 (by decide)
  have h1 : Entails.eval a c6696 := h 6695 (by decide)
  have h2 : Entails.eval a c7257 := h 7256 (by decide)
  have h3 : Entails.eval a c7166 := h 7165 (by decide)
  have h4 : Entails.eval a c6952 := h 6951 (by decide)
  have h5 : Entails.eval a c6307 := h 6306 (by decide)
  have h6 : Entails.eval a c7418 := h 7417 (by decide)
  have h7 : Entails.eval a c8124 := derived8124 a h
  have h8 : Entails.eval a c419 := h 418 (by decide)
  have h9 : Entails.eval a c412 := h 411 (by decide)
  have h10 : Entails.eval a c436 := h 435 (by decide)
  have h11 : Entails.eval a c2410 := h 2409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8240 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨62, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, true), (⟨60, by decide⟩, false), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8240 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c419, some c436, some c410, some c2446, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8240 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8240 : lratChecker f8240 p8240 = .success := by decide +kernel
theorem unsat8240 : Unsatisfiable (PosFin 65) f8240 := by
  apply lratCheckerSound f8240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8240
  · intro a ha; simp [p8240] at ha; subst a; trivial
  · exact checked8240
theorem derived8240 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8240 := by
  apply localUnsat_implies_entails f8240 [c419, c436, c410, c2446] c8240 unsat8240 (by rfl) a
  have h0 : Entails.eval a c419 := h 418 (by decide)
  have h1 : Entails.eval a c436 := h 435 (by decide)
  have h2 : Entails.eval a c410 := h 409 (by decide)
  have h3 : Entails.eval a c2446 := h 2445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8241 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false), (⟨60, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8241 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2427, some c2523, some c2487, some c3802, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8241 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8241 : lratChecker f8241 p8241 = .success := by decide +kernel
theorem unsat8241 : Unsatisfiable (PosFin 65) f8241 := by
  apply lratCheckerSound f8241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8241
  · intro a ha; simp [p8241] at ha; subst a; trivial
  · exact checked8241
theorem derived8241 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8241 := by
  apply localUnsat_implies_entails f8241 [c2427, c2523, c2487, c3802] c8241 unsat8241 (by rfl) a
  have h0 : Entails.eval a c2427 := h 2426 (by decide)
  have h1 : Entails.eval a c2523 := h 2522 (by decide)
  have h2 : Entails.eval a c2487 := h 2486 (by decide)
  have h3 : Entails.eval a c3802 := h 3801 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8242 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, true), (⟨60, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8242 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8075, some c8160, some c8189, some c8211, some c8232, some c8220, some c8233, some c8237, some c8239, some c8241, some c454, some c457, some c3114, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8242 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8242 : lratChecker f8242 p8242 = .success := by decide +kernel
theorem unsat8242 : Unsatisfiable (PosFin 65) f8242 := by
  apply lratCheckerSound f8242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8242
  · intro a ha; simp [p8242] at ha; subst a; trivial
  · exact checked8242
theorem derived8242 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8242 := by
  apply localUnsat_implies_entails f8242 [c7994, c8075, c8160, c8189, c8211, c8232, c8220, c8233, c8237, c8239, c8241, c454, c457, c3114] c8242 unsat8242 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8075 := derived8075 a h
  have h2 : Entails.eval a c8160 := derived8160 a h
  have h3 : Entails.eval a c8189 := derived8189 a h
  have h4 : Entails.eval a c8211 := derived8211 a h
  have h5 : Entails.eval a c8232 := derived8232 a h
  have h6 : Entails.eval a c8220 := derived8220 a h
  have h7 : Entails.eval a c8233 := derived8233 a h
  have h8 : Entails.eval a c8237 := derived8237 a h
  have h9 : Entails.eval a c8239 := derived8239 a h
  have h10 : Entails.eval a c8241 := derived8241 a h
  have h11 : Entails.eval a c454 := h 453 (by decide)
  have h12 : Entails.eval a c457 := h 456 (by decide)
  have h13 : Entails.eval a c3114 := h 3113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8243 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, true), (⟨60, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8243 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8237, some c7994, some c8189, some c8211, some c8220, some c8232, some c8233, some c6681, some c6696, some c7257, some c7166, some c6952, some c6307, some c7418, some c8160, some c8075, some c8239, some c8242, some c481, some c8238, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8243 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8243 : lratChecker f8243 p8243 = .success := by decide +kernel
theorem unsat8243 : Unsatisfiable (PosFin 65) f8243 := by
  apply lratCheckerSound f8243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8243
  · intro a ha; simp [p8243] at ha; subst a; trivial
  · exact checked8243
theorem derived8243 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8243 := by
  apply localUnsat_implies_entails f8243 [c8237, c7994, c8189, c8211, c8220, c8232, c8233, c6681, c6696, c7257, c7166, c6952, c6307, c7418, c8160, c8075, c8239, c8242, c481, c8238] c8243 unsat8243 (by rfl) a
  have h0 : Entails.eval a c8237 := derived8237 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8211 := derived8211 a h
  have h4 : Entails.eval a c8220 := derived8220 a h
  have h5 : Entails.eval a c8232 := derived8232 a h
  have h6 : Entails.eval a c8233 := derived8233 a h
  have h7 : Entails.eval a c6681 := h 6680 (by decide)
  have h8 : Entails.eval a c6696 := h 6695 (by decide)
  have h9 : Entails.eval a c7257 := h 7256 (by decide)
  have h10 : Entails.eval a c7166 := h 7165 (by decide)
  have h11 : Entails.eval a c6952 := h 6951 (by decide)
  have h12 : Entails.eval a c6307 := h 6306 (by decide)
  have h13 : Entails.eval a c7418 := h 7417 (by decide)
  have h14 : Entails.eval a c8160 := derived8160 a h
  have h15 : Entails.eval a c8075 := derived8075 a h
  have h16 : Entails.eval a c8239 := derived8239 a h
  have h17 : Entails.eval a c8242 := derived8242 a h
  have h18 : Entails.eval a c481 := h 480 (by decide)
  have h19 : Entails.eval a c8238 := derived8238 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8244 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨62, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, true), (⟨60, by decide⟩, false), (⟨39, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8244 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c481, some c8238, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8244 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8244 : lratChecker f8244 p8244 = .success := by decide +kernel
theorem unsat8244 : Unsatisfiable (PosFin 65) f8244 := by
  apply lratCheckerSound f8244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8244
  · intro a ha; simp [p8244] at ha; subst a; trivial
  · exact checked8244
theorem derived8244 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8244 := by
  apply localUnsat_implies_entails f8244 [c481, c8238] c8244 unsat8244 (by rfl) a
  have h0 : Entails.eval a c481 := h 480 (by decide)
  have h1 : Entails.eval a c8238 := derived8238 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8245 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨62, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, true), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8245 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1519, some c1936, some c520, some c522, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8245 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8245 : lratChecker f8245 p8245 = .success := by decide +kernel
theorem unsat8245 : Unsatisfiable (PosFin 65) f8245 := by
  apply lratCheckerSound f8245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8245
  · intro a ha; simp [p8245] at ha; subst a; trivial
  · exact checked8245
theorem derived8245 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8245 := by
  apply localUnsat_implies_entails f8245 [c1519, c1936, c520, c522] c8245 unsat8245 (by rfl) a
  have h0 : Entails.eval a c1519 := h 1518 (by decide)
  have h1 : Entails.eval a c1936 := h 1935 (by decide)
  have h2 : Entails.eval a c520 := h 519 (by decide)
  have h3 : Entails.eval a c522 := h 521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8246 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, true), (⟨60, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8246 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8243, some c8237, some c7994, some c8189, some c8211, some c8220, some c8232, some c8233, some c6681, some c6696, some c7257, some c7166, some c6952, some c6307, some c7418, some c8160, some c8240, some c8244, some c8245, some c499, some c538, some c2965, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8246 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8246 : lratChecker f8246 p8246 = .success := by decide +kernel
theorem unsat8246 : Unsatisfiable (PosFin 65) f8246 := by
  apply lratCheckerSound f8246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8246
  · intro a ha; simp [p8246] at ha; subst a; trivial
  · exact checked8246
theorem derived8246 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8246 := by
  apply localUnsat_implies_entails f8246 [c8243, c8237, c7994, c8189, c8211, c8220, c8232, c8233, c6681, c6696, c7257, c7166, c6952, c6307, c7418, c8160, c8240, c8244, c8245, c499, c538, c2965] c8246 unsat8246 (by rfl) a
  have h0 : Entails.eval a c8243 := derived8243 a h
  have h1 : Entails.eval a c8237 := derived8237 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8189 := derived8189 a h
  have h4 : Entails.eval a c8211 := derived8211 a h
  have h5 : Entails.eval a c8220 := derived8220 a h
  have h6 : Entails.eval a c8232 := derived8232 a h
  have h7 : Entails.eval a c8233 := derived8233 a h
  have h8 : Entails.eval a c6681 := h 6680 (by decide)
  have h9 : Entails.eval a c6696 := h 6695 (by decide)
  have h10 : Entails.eval a c7257 := h 7256 (by decide)
  have h11 : Entails.eval a c7166 := h 7165 (by decide)
  have h12 : Entails.eval a c6952 := h 6951 (by decide)
  have h13 : Entails.eval a c6307 := h 6306 (by decide)
  have h14 : Entails.eval a c7418 := h 7417 (by decide)
  have h15 : Entails.eval a c8160 := derived8160 a h
  have h16 : Entails.eval a c8240 := derived8240 a h
  have h17 : Entails.eval a c8244 := derived8244 a h
  have h18 : Entails.eval a c8245 := derived8245 a h
  have h19 : Entails.eval a c499 := h 498 (by decide)
  have h20 : Entails.eval a c538 := h 537 (by decide)
  have h21 : Entails.eval a c2965 := h 2964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8247 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨35, by decide⟩, false), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8247 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c533, some c475, some c493, some c2946, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8247 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8247 : lratChecker f8247 p8247 = .success := by decide +kernel
theorem unsat8247 : Unsatisfiable (PosFin 65) f8247 := by
  apply lratCheckerSound f8247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8247
  · intro a ha; simp [p8247] at ha; subst a; trivial
  · exact checked8247
theorem derived8247 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8247 := by
  apply localUnsat_implies_entails f8247 [c533, c475, c493, c2946] c8247 unsat8247 (by rfl) a
  have h0 : Entails.eval a c533 := h 532 (by decide)
  have h1 : Entails.eval a c475 := h 474 (by decide)
  have h2 : Entails.eval a c493 := h 492 (by decide)
  have h3 : Entails.eval a c2946 := h 2945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8248 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8248 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2946, some c3134, some c3115, some c3686, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8248 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8248 : lratChecker f8248 p8248 = .success := by decide +kernel
theorem unsat8248 : Unsatisfiable (PosFin 65) f8248 := by
  apply lratCheckerSound f8248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8248
  · intro a ha; simp [p8248] at ha; subst a; trivial
  · exact checked8248
theorem derived8248 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8248 := by
  apply localUnsat_implies_entails f8248 [c2946, c3134, c3115, c3686] c8248 unsat8248 (by rfl) a
  have h0 : Entails.eval a c2946 := h 2945 (by decide)
  have h1 : Entails.eval a c3134 := h 3133 (by decide)
  have h2 : Entails.eval a c3115 := h 3114 (by decide)
  have h3 : Entails.eval a c3686 := h 3685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8249 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨61, by decide⟩, true), (⟨60, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8249 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8237, some c7994, some c8189, some c8211, some c8220, some c8232, some c8233, some c6681, some c6696, some c7257, some c7166, some c6952, some c6307, some c7418, some c8160, some c8243, some c8246, some c8247, some c8238, some c8248, some c514, some c452, some c2588, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8249 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8249 : lratChecker f8249 p8249 = .success := by decide +kernel
theorem unsat8249 : Unsatisfiable (PosFin 65) f8249 := by
  apply lratCheckerSound f8249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8249
  · intro a ha; simp [p8249] at ha; subst a; trivial
  · exact checked8249
theorem derived8249 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8249 := by
  apply localUnsat_implies_entails f8249 [c8237, c7994, c8189, c8211, c8220, c8232, c8233, c6681, c6696, c7257, c7166, c6952, c6307, c7418, c8160, c8243, c8246, c8247, c8238, c8248, c514, c452, c2588] c8249 unsat8249 (by rfl) a
  have h0 : Entails.eval a c8237 := derived8237 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8189 := derived8189 a h
  have h3 : Entails.eval a c8211 := derived8211 a h
  have h4 : Entails.eval a c8220 := derived8220 a h
  have h5 : Entails.eval a c8232 := derived8232 a h
  have h6 : Entails.eval a c8233 := derived8233 a h
  have h7 : Entails.eval a c6681 := h 6680 (by decide)
  have h8 : Entails.eval a c6696 := h 6695 (by decide)
  have h9 : Entails.eval a c7257 := h 7256 (by decide)
  have h10 : Entails.eval a c7166 := h 7165 (by decide)
  have h11 : Entails.eval a c6952 := h 6951 (by decide)
  have h12 : Entails.eval a c6307 := h 6306 (by decide)
  have h13 : Entails.eval a c7418 := h 7417 (by decide)
  have h14 : Entails.eval a c8160 := derived8160 a h
  have h15 : Entails.eval a c8243 := derived8243 a h
  have h16 : Entails.eval a c8246 := derived8246 a h
  have h17 : Entails.eval a c8247 := derived8247 a h
  have h18 : Entails.eval a c8238 := derived8238 a h
  have h19 : Entails.eval a c8248 := derived8248 a h
  have h20 : Entails.eval a c514 := h 513 (by decide)
  have h21 : Entails.eval a c452 := h 451 (by decide)
  have h22 : Entails.eval a c2588 := h 2587 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8250 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨56, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨55, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8250 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c479, some c535, some c497, some c2959, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p8250 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8250 : lratChecker f8250 p8250 = .success := by decide +kernel
theorem unsat8250 : Unsatisfiable (PosFin 65) f8250 := by
  apply lratCheckerSound f8250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8250
  · intro a ha; simp [p8250] at ha; subst a; trivial
  · exact checked8250
theorem derived8250 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8250 := by
  apply localUnsat_implies_entails f8250 [c479, c535, c497, c2959] c8250 unsat8250 (by rfl) a
  have h0 : Entails.eval a c479 := h 478 (by decide)
  have h1 : Entails.eval a c535 := h 534 (by decide)
  have h2 : Entails.eval a c497 := h 496 (by decide)
  have h3 : Entails.eval a c2959 := h 2958 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8250

end CochromaticTwenty.Certificates.FixedCore0
